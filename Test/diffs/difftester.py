#!/usr/bin/env python3
"""A differential tester for Dafny.

This program takes a list of Dafny executables (either the CLI or the LSP
server) and a list of snapshots and runs them through Dafny's CLI as well as
through Dafny's LSP server.  Verification results are then compared to ensure
that they match.

Limitations:

- This only checks error messages, not return codes

- This only checks for errors in one "main" file, not in all files reported by
  the LSP server.

Example usage::

   ./difftester.py --driver Dafny \
                   --driver DafnyLanguageServer \
                   --input snaps.dfy
"""

from typing import (
    Any, Callable, Dict, Iterable, Iterator, IO, List, Optional, Tuple, TypeVar,
    Union, overload
)

import argparse
import json
import os
import platform
import re
import shlex
import shutil
import subprocess
import sys

from collections import deque
from concurrent.futures import ThreadPoolExecutor
from itertools import zip_longest
from pathlib import Path
from subprocess import PIPE
from pprint import pformat
from textwrap import indent

# For ordered dicts and f-strings
assert sys.version_info >= (3, 7)

T = TypeVar("T")
Json = Dict[str, Any]

LSPMessage = Json
"""A single LSP client request."""

VerificationResult = List[str]
"""Structured output returned by Dafny."""

FIXME = NotImplementedError
DEBUG = False
INPUT_TEE = "inputs.log"
OUTPUT_TEE = "outputs.log"

NWORKERS = 1
TIMEOUT = 120.0  # https://stackoverflow.com/questions/1408356/


@overload
def which(exe: str) -> str: ...
@overload
def which(exe: List[str]) -> List[str]: ...

def which(exe: Union[str, List[str]]) -> Union[str, List[str]]:
    """Locate executable `exe`; raise a ``ValueError`` if it can't be found."""
    if isinstance(exe, list):
        return [which(exe[0]), *exe[1:]]
    path = shutil.which(exe)
    if path is None:
        raise ValueError(f"Executable not found in PATH: {exe}")
    return path


def debug(prefix: str, *msgs: str, **kwds: Dict[str, Any]) -> None:
    """Print `msgs` with `prefix`; forward `kwds` to ``print``."""
    if DEBUG:
        print(prefix, *msgs, **{**kwds, "file": sys.stderr}) # type: ignore


def _no_window() -> subprocess.STARTUPINFO:
    """Create a startupinfo object.

    On Windows, set it up to run without showing a command window.
    """
    si = subprocess.STARTUPINFO()
    if platform.system() == "Windows":
        # No new window
        si.dwFlags |= subprocess.STARTF_USESHOWWINDOW
        # “Terminate batch job?” on Ctrl+C, but that blocks the parent process
        # si.dwFlags |= subprocess.CREATE_NEW_PROCESS_GROUP
    return si


class InputTee(IO[bytes]):
    """Wrapper around a collection of streams that broadcasts writes."""

    def __init__(self, *streams: IO[bytes]) -> None:
        self.streams = streams

    def close(self) -> None:
        for s in self.streams:
            s.close()

    def write(self, data: bytes) -> int:
        return max(s.write(data) for s in self.streams)

    def flush(self) -> None:
        for s in self.streams:
            s.flush()


class RecorderTee(IO[bytes]):
    """Wrapper around a stream that records reads from it."""

    def __init__(self, stream: IO[bytes], log: IO[bytes]) -> None:
        self.stream, self.log = stream, log

    def read(self, n: int) -> bytes:
        bs = self.stream.read(n)
        self.log.write(bs)
        return bs

    def readline(self) -> bytes:
        bs = self.stream.readline()
        self.log.write(bs)
        return bs

    def close(self) -> None:
        for s in (self.stream, self.log):
            s.close()

    def flush(self) -> None:
        self.log.flush()


class Snapshot:
    """The contents of a Dafny file."""

    def __init__(self, name: str, contents: str) -> None:
        self.name = name
        self.contents = contents

    @staticmethod
    def from_file(path: Union[str, Path]) -> "Snapshot":
        pth = Path(path)
        return Snapshot(pth.name, pth.read_text(encoding="utf-8"))

    def __str__(self) -> str:
        return self.contents


class ProverInputs:
    """A sequence of inputs to Dafny."""

    name: str

    def as_lsp(self) -> "LSPTrace":
        """Convert self into an LSP trace."""
        raise NotImplementedError

    def as_snapshots(self) -> "Snapshots":
        """Convert self into a sequence of snapshots."""
        raise NotImplementedError

    def __len__(self) -> int:
        raise NotImplementedError


class ProverOutput:
    """An output of Dafny."""

    # @property
    # def errors(self) -> List[VerificationResult]:
    #     """Normalize this output and convert it to a list of results."""
    #     raise NotImplementedError

    # Strings are easier to diff than structured data, especially when looking
    # at insertions/deletions.
    def format(self) -> str:
        """Normalize this output and convert it to a string."""
        raise NotImplementedError

    @property
    def raw(self) -> str:
        """Return the raw output of the prover."""
        raise NotImplementedError


class LSPMethods:
    """Global constants for LSP Methods."""
    didOpen = "textDocument/didOpen"
    didChange = "textDocument/didChange"
    publishDiagnostics = "textDocument/publishDiagnostics"
    compilationStatus = "dafny/compilation/status"
    NEED_DIAGNOSTICS = {didOpen, didChange}


class LSPTrace(ProverInputs):
    """A sequence of messages sent by an LSP client."""

    def __init__(self, name: str, commands: Iterable[LSPMessage]) -> None:
        self.name = name
        self.messages: List[LSPMessage] = list(commands)

    @classmethod
    def from_json(cls, fname: str) -> "LSPTrace":
        """Load an LSP trace from a file containing JSON."""
        with open(fname, encoding="utf-8") as f:
            return LSPTrace(fname, json.load(f))

    def as_lsp(self) -> "LSPTrace":
        """Convert self into an LSP trace."""
        return self

    def _iter_snapshots(self) -> Iterable[str]:
        for msg in self.messages:
            if msg["method"] == LSPMethods.didOpen:
                yield msg["params"]["textDocument"]["text"]
            if msg["method"] == LSPMethods.didChange:
                for change in msg["params"]["contentChanges"]:
                    yield change["text"]  # FIXME add support for ranges

    @property
    def uri(self) -> str:
        """Return the current document's URI."""
        for m in self.messages:
            if m["method"] == LSPMethods.didOpen:
                return m["textDocument"]["uri"] # type: ignore
        raise ValueError("No didOpen message found in LSP trace.")

    def as_snapshots(self) -> "Snapshots":
        """Convert self into a sequence of snapshots."""
        snapshots = (Snapshot(self.name, s) for s in self._iter_snapshots())
        return Snapshots(self.name, self.uri, snapshots)

    def __len__(self) -> int:
        return sum(msg["method"] in (LSPMethods.didOpen, LSPMethods.didChange)
                   for msg in self.messages)


class Snapshots(ProverInputs):
    """A sequence of Dafny files."""

    VERNUM_RE = re.compile(r"\A(?P<stem>.*)[.]v(?P<num>[0-9]+)\Z")

    def __init__(self, name: str, uri: str, snapshots: Iterable[Snapshot]) -> None:
        self.name = name
        self.uri = uri
        self.snapshots = list(snapshots)

    @classmethod
    def strip_vernum(cls, fname: Union[str, Path]) -> Tuple[str, Optional[int], str]:
        """Split `fname` into a stem, a suffix, and a version number.

        >>> Snapshots.strip_vernum("a.v0.dfy")
        ('a', 0, '.dfy')
        >>> Snapshots.strip_vernum("a.dfy")
        ('a', None, '.dfy')
        """
        pth = Path(fname)
        mnum = cls.VERNUM_RE.match(pth.stem)
        if not mnum:
            return pth.stem, None, pth.suffix
        return mnum.group("stem"), int(mnum.group("num")), pth.suffix


    @classmethod
    def _find_snapshot_files(cls, name: str) -> Iterable[Tuple[int, Path]]:
        """Yield paths matching stem.vN.suffix where stem.suffix is `name`."""
        ref = Path(name)
        if ref.exists():
            yield 0, ref
            return
        for f in ref.parent.iterdir():
            stem, num, suffix = cls.strip_vernum(f)
            if ref.stem == stem and ref.suffix == suffix and num is not None:
                yield num, f

    @classmethod
    def from_files(cls, name: str) -> "Snapshots":
        """Read file `name` from file.

        If `name` does not exist, read all files matching stem.vN.suffix, where
        stem.suffix is `name`.
        """
        files = [f for _, f in sorted(cls._find_snapshot_files(name))]
        snaps = (Snapshot.from_file(f) for f in files)
        uri = Path(name).absolute().as_uri()
        return Snapshots(name, uri, snaps)

    @classmethod
    def _complete_range(cls, previous: Snapshot) -> Json:
        contents = str(previous)
        last_line = contents.count("\n")
        last_bol = contents.rfind("\n") + 1
        last_pos = len(contents[last_bol:].encode("utf-16le"))
        return {"start": {"line": 0, "character": 0},
                "end": {"line": last_line, "character": last_pos}}

    @classmethod
    def _lsp_of_snapshot(cls, uri: str, version: int, snapshot: Snapshot,
                         previous: Optional[Snapshot]) -> LSPMessage:
        document = {"uri": uri, "languageId": "dafny", "version": version}
        return {
            "method": LSPMethods.didOpen,
            "params": {"textDocument": {**document, "text": str(snapshot)}}
        } if previous is None else {
            "method": LSPMethods.didChange,
            "params": {"textDocument": document,
                       "contentChanges": [{
                           "text": str(snapshot),
                           "range": cls._complete_range(previous)
                       }]}
        }

    def _iter_lsp(self) -> Iterable[LSPMessage]:
        yield {
            "method": "initialize",
            "params": {"processId": os.getpid(),
                       "clientInfo": {"name": "Dafny diff tester"},
                       "rootUri": Path(os.getcwd()).as_uri(),
                       "capabilities": {"publishDiagnostics": {}}}
        }
        yield {"method": "initialized", "params": {}}
        prev = None
        for version, snap in enumerate(self.snapshots):
            yield self._lsp_of_snapshot(self.uri, version, snap, prev)
            prev = snap
        yield {"method": "shutdown", "params": {}}
        yield {"method": "exit", "params": {}}

    def _iter_jrpc(self) -> Iterable[LSPMessage]:
        METHODS = {"initialize", "shutdown"}
        for id, msg in enumerate(self._iter_lsp()):
            idd = {"id": id} if msg["method"] in METHODS else {}
            yield {"jsonrpc": "2.0", **msg, **idd}

    def as_lsp(self) -> "LSPTrace":
        """Convert self into an LSP trace."""
        return LSPTrace(self.name, self._iter_jrpc())

    def as_snapshots(self) -> "Snapshots":
        """Convert self into a sequence of snapshots."""
        return self

    def __iter__(self) -> Iterator[Snapshot]:
        return iter(self.snapshots)

    def __len__(self) -> int:
        return len(self.snapshots)

class Driver:
    """Abstract interface for Dafny drivers."""

    def __init__(self, command: List[str]) -> None:
        self.command = which(command)

    def run(self, inputs: ProverInputs) -> Iterable[ProverOutput]:
        """Run `inputs` and return the prover's outputs."""
        raise NotImplementedError()

    def __repr__(self) -> str:
        return f"{type(self).__name__}(command={self.command})"


class LSPServer:
    """A simpler wrapper aroudn the Dafny LSP server."""

    ARGS = ["--documents:verify=onchange",
            "--verifier:timelimit=0",
            "--verifier:vcscores=0",
            "--ghost:markStatements=true"]  # FIXME

    def __init__(self, command: List[str]) -> None:
        self.command = command
        self.repl: "Optional[subprocess.Popen[bytes]]" = None
        self.pending_output: Dict[bytes, LSPMessage] = {}  # Random access queue

    @staticmethod
    def _dump(cmd: LSPMessage) -> str:
        js = json.dumps(cmd, indent=1)
        # \r\n for consistency, final newline for readability
        return js.replace("\n", "\r\n") + "\r\n"

    def send(self, cmd: LSPMessage) -> None:
        """Send a request to the server."""
        assert self.repl
        assert self.repl.stdin
        js = self._dump(cmd)
        header = f"Content-Length: {len(js)}\r\n\r\n"
        debug(">>", repr(header))
        debug(">>", js)
        self.repl.stdin.write(header.encode("utf-8"))
        self.repl.stdin.write(js.encode("utf-8"))
        self.repl.stdin.flush()

    HEADER_RE = re.compile(r"Content-Length: (?P<len>[0-9]+)\r\n")

    def _receive(self) -> Tuple[bytes, Json]:
        assert self.repl
        assert self.repl.stdout
        line, length = None, None
        while line not in ("", "\r\n"):
            line = self.repl.stdout.readline().decode("utf-8")
            debug("<<", repr(line))
            header = self.HEADER_RE.match(line)
            if header:
                length = int(header.group("len"))
        if length is None:
            MSG = (f"Unexpected output: {line!r}, use --debug for more info."
                   "If --debug doesn't help, check Dafny's server logs "
                   "(https://github.com/dafny-lang/ide-vscode#debugging).")
            raise ValueError(MSG)
        response: bytes = self.repl.stdout.read(length)
        if len(response) != length:
            raise ValueError(f"Truncated response: {response!r}")
        resp = response.decode("utf-8")
        debug("<<", resp)
        js = json.loads(resp)
        self.pending_output[response] = js
        return (response, js)

    def receive(self, pred: Callable[[LSPMessage], bool]) -> LSPMessage:
        """Read server messages until finding one that matches `pred`."""
        msgs = iter(list(self.pending_output.items()))
        while True:
            key, msg = next(msgs, None) or self._receive() # type: ignore
            if pred(msg):
                del self.pending_output[key]
                return msg

    def discard_pending_messages(self):
        """Discard pending server messages."""
        self.pending_output.clear()

    def _kill(self) -> None:
        assert self.repl and self.repl.stdin and self.repl.stdout
        self.repl.kill()
        try:
            self.repl.stdin.close()
            self.repl.stdout.close()
        finally:
            self.repl.wait()

    def kill(self) -> "Optional[subprocess.Popen[bytes]]":
        """Terminate this Dafny instance."""
        repl = self.repl
        if self.repl:
            self._kill()
            self.repl = None
            self.pending_output = {}
        return repl

    def _start(self) -> None:
        self.kill()

        cmd =  [*self.command, *self.ARGS]
        debug("#", shlex.join(cmd))

        # pylint: disable=consider-using-with
        self.repl = subprocess.Popen(
            cmd, startupinfo=_no_window(),
            stdin=PIPE, stderr=PIPE, stdout=PIPE)

        if INPUT_TEE:
            assert self.repl.stdin
            log = open(INPUT_TEE, mode="wb")
            self.repl.stdin = InputTee(self.repl.stdin, log) # type: ignore

        if OUTPUT_TEE:
            assert self.repl.stdout
            log = open(OUTPUT_TEE, mode="wb")
            self.repl.stdout = RecorderTee(self.repl.stdout, log) # type: ignore

    def __enter__(self) -> "LSPServer":
        """Start a Dafny LSP server."""
        self._start()
        return self

    def __exit__(self, *_exn: Any) -> None:
        """Kill the current Dafny LSP server."""
        self.kill()


class LSPOutput(ProverOutput):
    LEVELS = {1: "Error", }

    def __init__(self, diagnostics: List[Dict[str, Any]]) -> None:
        self.diags = sorted(diagnostics, key=self._key)

    @classmethod
    def _format_diag(cls, d: LSPMessage) -> str:
        msg = d["message"]
        kind = cls.LEVELS[d["severity"]]
        pos = d['range']['start']
        l, c = pos['line'] + 1, pos['character']
        return f"<stdin>({l},{c}): {kind}: {msg}"

    @staticmethod
    def _key(d) -> Tuple[int, int, int, int]:
        start, end = d['range']['start'], d['range']['end']
        return start['line'], start['character'], end['line'], end['character']

    def format(self) -> str:
        """Format to a string matching Dafny's CLI output."""
        diags = sorted(self.diags, key=self._key)
        return "\n".join(self._format_diag(d) for d in diags)

    @property
    def raw(self) -> str:
        """Return the raw output of the prover."""
        return self.diags


class LSPDriver(Driver):
    """A driver using Dafny's LSP implementation."""

    @staticmethod
    def is_diagnostic_for(doc: Json) -> Callable[[LSPMessage], bool]:
        """Return a function that checks for diagnostics for `doc`."""
        def _filter(m: LSPMessage) -> bool:
            if m["method"] == LSPMethods.publishDiagnostics:
                mp = m["params"]
                return (mp["version"] == doc["version"] and # type: ignore
                        mp["uri"] == doc["uri"])
            return False
        return _filter

    @staticmethod
    def is_response_to(id: int) -> Callable[[LSPMessage], bool]:
        """Return a function that checks for responses to `id`."""
        return lambda m: m.get("id") == id

    @staticmethod
    def is_verified_notification() -> Callable[[LSPMessage], bool]:
        """Return a function that checks for a message indicating completion."""
        def _filter(m: LSPMessage) -> bool:
            if m["method"] == LSPMethods.compilationStatus:
                st = m["params"]["status"]
                return "Suceeded" in st or "Failed" in st
            return False
        return _filter

    def _iter_results(self, messages: Iterable[LSPMessage]) \
            -> Iterable[LSPOutput]:
        """Feed `inputs` to Dafny's LSP server; return diagnostic messages."""
        with LSPServer(self.command) as server:
            for msg in messages:
                server.discard_pending_messages() # Drop stale output
                server.send(msg)
                if msg["method"] in LSPMethods.NEED_DIAGNOSTICS:
                    doc = msg["params"]["textDocument"]
                    _ = server.receive(self.is_verified_notification())
                    server.discard_pending_messages() # Drop in-progress diagnostics
                    diag = server.receive(self.is_diagnostic_for(doc))
                    yield LSPOutput(diag["params"]["diagnostics"])
                if "id" in msg:  # Wait for response
                    server.receive(self.is_response_to(msg["id"]))

    def run(self, inputs: ProverInputs) -> Iterable[ProverOutput]:
        """Run `inputs` through Dafny's LSP server; return diagnostics."""
        messages = inputs.as_lsp().messages
        yield from self._iter_results(messages)


class CLIOutput(ProverOutput):
    ERROR_PATTERN = re.compile(r"^.*?[(][0-9]+,[0-9]+[)].*")

    def __init__(self, output: str) -> None:
        self.output = output

    def format(self) -> str:
        """Normalize the output of a single Dafny run for easier comparison."""
        messages = self.ERROR_PATTERN.finditer(self.output)
        return "\n".join(m.group() for m in messages)

    @property
    def raw(self) -> str:
        """Return the raw output of the prover."""
        return self.output

class CLIDriver(Driver):
    """A driver using Dafny's CLI."""

    ARGS = ["/compile:0", "/stdin"]

    def _exec(self, snapshot: Snapshot) -> "subprocess.CompletedProcess[str]":
        cmd = [*self.command, *self.ARGS]
        debug("#", shlex.join(cmd), "<", snapshot.name)
        return subprocess.run(
            cmd, check=False,
            input=str(snapshot), encoding="utf-8",
            startupinfo=_no_window(),
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)

    def _collect_one_output(self, snapshot: Snapshot) -> CLIOutput:
        return CLIOutput(self._exec(snapshot).stdout)

    def _iter_results(self, snapshots: Snapshots) -> Iterable[CLIOutput]:
        with ThreadPoolExecutor(max_workers=NWORKERS) as exc:
            yield from exc.map(self._collect_one_output,
                               snapshots, timeout=TIMEOUT)

    def run(self, inputs: ProverInputs) -> Iterable[ProverOutput]:
        """Run `inputs` through Dafny's CLI; return the prover's outputs."""
        yield from self._iter_results(inputs.as_snapshots())


def window(stream: Iterable[T], n: int) -> Iterable[Tuple[T, ...]]:
    """Iterate over `n`-element windows of `stream`."""
    win: "deque[T]" = deque(maxlen=n)
    for token in stream:
        win.append(token)
        if len(win) == n:
            yield tuple(win)


def test(inputs: ProverInputs, *drivers: Driver) -> None:
    """Run `inputs` through each one of `drivers` and report any mismatches."""
    snapshots = inputs.as_snapshots()
    prover_output_streams = [d.run(inputs) for d in drivers]
    # zip() would be unsafe here (it wouldn't exhaust the iterator over the LSP
    # server's results and hence wouldn't send the “shutdown” message).
    results = zip_longest(*prover_output_streams)
    for snapidx, snap in enumerate(snapshots):
        print(f"------ {snap.name}(#{snapidx}) ------", flush=True)
        prover_outputs = next(results)
        for (d1, p1), (d2, p2) in window(zip(drivers, prover_outputs), 2):
            o1, o2 = p1.format(), p2.format()
            if o1 != o2:
                print("!! Output mismatch")
                print(f"   For input {snap.name}(#{snapidx}),")
                print(f"   Driver {d1} produced this output:")
                print(indent(o1, "   > "))
                print(f"   Driver {d2} produced this output:")
                print(indent(o2, "   > "))
                print("   Raw output:")
                print(indent(pformat(p1.raw), "   > "))
                print("   --------------------------------")
                print(indent(pformat(p2.raw), "   > "))
        sys.stdout.flush()
    for _ in results:
        # Exhaust results iterators to make sure LSPServer calls shutdown and
        # exit (otherwise the final code of these iterators remains pending).
        assert False


SLASH_2DASHES = re.compile("^/(?=--)")


def resolve_driver(command: List[str]) -> Driver:
    """Resolve `command` into a ``Driver`` instance."""
    command = [SLASH_2DASHES.sub("", c) for c in command]
    if "DafnyLanguageServer" in command[0]:
        return LSPDriver(command)
    return CLIDriver(command)


def resolve_input(inp: str, parser: argparse.ArgumentParser) -> ProverInputs:
    """Resolve file name `inp` into a ``ProverInputs`` instance.

    Report errors through `parser`."""
    stem, num, suffix = Snapshots.strip_vernum(inp)

    if num:
        MSG = (f"WARNING: File name {inp} looks like a single snapshot.  "
               f"To verify multiple snapshots, call this program on "
               f"{stem}{suffix}.")

    if suffix != ".dfy":
        MSG = (f"{inp}: Unsupported file extension {suffix!r} "
               "(only .dfy inputs are supported for now).")
        parser.error(MSG)

    return Snapshots.from_files(inp)

def parse_arguments() -> argparse.Namespace:
    """Parser command line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)

    parser.add_argument("--debug", action="store_true")

    J_HELP = "Run command line tests in N concurrent threads."
    parser.add_argument("-j", type=int, default=None,
                        metavar="N", help=J_HELP)

    TIMEOUT_HELP = "Limit execution time to N seconds for individual CLI runs."
    parser.add_argument("--timeout", type=int, default=None,
                        metavar="N", help=TIMEOUT_HELP)

    parser.add_argument("--driver", required=True,
                        nargs="+", action="append", dest="drivers",
                        metavar=("DRIVER_NAME", "ARGUMENTS"),
                        help="Register a driver")

    parser.add_argument("--input", required=True,
                        action="append", dest="inputs",
                        help="Register an input file")

    args, argv = parser.parse_known_args()
    if argv:
        MSG = (f"Unrecognized arguments: {' '.join(argv)}.  "
               "If these were meant as arguments to a --driver, "
               "prefix them with a slash.  For example, use "
               "/--verifier:cachingPolicy=0 instead of "
               "--verifier:cachingPolicy=0.")
        parser.error(MSG)
    args.drivers = [resolve_driver(d) for d in args.drivers]
    args.inputs = [resolve_input(d, parser) for d in args.inputs]

    if args.debug:
        global DEBUG
        DEBUG = True

    if args.j:
        global NWORKERS
        NWORKERS = args.j

    if args.timeout:
        global TIMEOUT
        TIMEOUT = args.timeout

    return args


def main() -> None:
    args = parse_arguments()
    for inputs in args.inputs:
        print(f"====== {inputs.name} ======", file=sys.stderr)
        test(inputs, *args.drivers)

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        pass
    # _test_diff()
    # _test_snapshots()
    # _test_snapshots_lsp()

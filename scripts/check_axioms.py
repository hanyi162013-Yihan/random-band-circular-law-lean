#!/usr/bin/env python3
"""Run every section axiom audit and enforce the logical-axiom allowlist.

Lean's ``#print axioms`` is informational, so a successful Lean exit alone
does not establish that the printed dependencies satisfy an allowlist.
Each source command must produce exactly one matching report; intentionally
repeated commands in an audit are counted separately.

The two report formats are those emitted by ``printAxiomsOf`` in
Lean 4.33.0's ``Lean/Elab/Print.lean``. Lists may wrap across lines.
``--self-test`` exercises only the parser and never invokes Lean.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import subprocess
import sys
import unittest


ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
SOURCE_COMMAND = re.compile(r"^[ \t]*#print[ \t]+axioms\b([^\n]*)$", re.MULTILINE)
SIMPLE_NAME = re.compile(r"[\w'.]+", re.UNICODE)
ANSI_ESCAPE = re.compile(r"\x1b\[[0-?]*[ -/]*[@-~]")
# Lean normally prints these information messages without a location prefix.
# Also accept its conventional `path:line:column: info:` prefix.
REPORT_PREFIX = r"^[ \t]*(?:[^\n]*?:[0-9]+:[0-9]+:[ \t]*(?:info|information):[ \t]*)?"
REPORT_HEADER = re.compile(
    REPORT_PREFIX + r"'([^\r\n]+)'[ \t]+(?:depends on axioms:|does not depend on any axioms)",
    re.MULTILINE,
)
REPORT = re.compile(
    REPORT_PREFIX
    + r"'(?P<name>[^\r\n]+)'[ \t]+(?:"
    + r"depends on axioms:[ \t\r\n]*\[(?P<axioms>[^\]]*)\]"
    + r"|(?P<none>does not depend on any axioms))"
    + r"[ \t]*\r?$",
    re.MULTILINE,
)


class AuditError(RuntimeError):
    """An audit did not establish all required allowlist checks."""


def mask_comments_and_strings(source: str) -> str:
    """Preserve line breaks while masking nested Lean comments and strings."""
    result: list[str] = []
    depth = 0
    in_string = False
    escaped = False
    i = 0
    while i < len(source):
        pair = source[i : i + 2]
        char = source[i]
        if depth:
            if pair == "/-":
                depth += 1
                result.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                result.extend("  ")
                i += 2
            else:
                result.append("\n" if char == "\n" else " ")
                i += 1
        elif in_string:
            result.append("\n" if char == "\n" else " ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            i += 1
        elif pair == "/-":
            depth = 1
            result.extend("  ")
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            if end == -1:
                end = len(source)
            result.extend(" " * (end - i))
            i = end
        elif char == '"':
            in_string = True
            result.append(" ")
            i += 1
        else:
            result.append(char)
            i += 1
    if depth or in_string:
        raise AuditError("unterminated Lean comment or string in audit source")
    return "".join(result)


def expected_declarations(source: str) -> Counter[str]:
    """Count the explicit, one-name-per-command audit declarations."""
    names: Counter[str] = Counter()
    for command in SOURCE_COMMAND.finditer(mask_comments_and_strings(source)):
        name = command.group(1).strip()
        if not SIMPLE_NAME.fullmatch(name):
            raise AuditError(f"unsupported #print axioms argument: {name!r}")
        names[name] += 1
    if not names:
        raise AuditError("audit source contains no #print axioms commands")
    return names


def format_counts(counts: Counter[str]) -> str:
    return ", ".join(f"{name} (x{count})" for name, count in sorted(counts.items()))


def validate_output(expected: Counter[str], output: str) -> int:
    """Require exact report multiplicities and allowlisted axiom dependencies."""
    if not expected:
        raise AuditError("expected declaration multiset is empty")
    clean = ANSI_ESCAPE.sub("", output)
    reports = list(REPORT.finditer(clean))
    headers = list(REPORT_HEADER.finditer(clean))
    if len(reports) != len(headers):
        raise AuditError("malformed or truncated #print axioms report")
    actual: Counter[str] = Counter()
    for report in reports:
        name = report.group("name")
        actual[name] += 1
        body = report.group("axioms")
        axioms = [] if body is None or not body.strip() else [
            item.strip() for item in body.split(",")
        ]
        if any(not item for item in axioms):
            raise AuditError(f"{name}: malformed axiom list")
        duplicates = Counter(axioms)
        if any(count > 1 for count in duplicates.values()):
            raise AuditError(f"{name}: duplicate item in axiom list")
        forbidden = set(axioms) - ALLOWED_AXIOMS
        if forbidden:
            raise AuditError(f"{name}: forbidden axioms: {', '.join(sorted(forbidden))}")
    missing = expected - actual
    extra = actual - expected
    if missing or extra:
        details = []
        if missing:
            details.append(f"missing reports: {format_counts(missing)}")
        if extra:
            details.append(f"unexpected or duplicate reports: {format_counts(extra)}")
        raise AuditError("; ".join(details))
    return sum(actual.values())


def discover_audits(root: Path) -> list[Path]:
    audits = {path for path in root.glob("Section*/**/*AxiomAudit.lean") if path.is_file()}
    root_audit = root / "AxiomAudit.lean"
    if root_audit.is_file():
        audits.add(root_audit)
    if not audits:
        raise AuditError("no axiom audit files found")
    return sorted(audits, key=lambda path: path.relative_to(root).as_posix())


def run_audits(root: Path) -> None:
    audits = discover_audits(root)
    total = 0
    for path in audits:
        relative = path.relative_to(root).as_posix()
        expected = expected_declarations(path.read_text(encoding="utf-8"))
        print(f"[axiom-audit] {relative}: {sum(expected.values())} reports expected", flush=True)
        completed = subprocess.run(
            ["lake", "env", "lean", relative],
            cwd=root,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            check=False,
        )
        if completed.stdout:
            print(completed.stdout, end="" if completed.stdout.endswith("\n") else "\n", flush=True)
        if completed.stderr:
            print(completed.stderr, file=sys.stderr,
                  end="" if completed.stderr.endswith("\n") else "\n", flush=True)
        if completed.returncode != 0:
            raise AuditError(f"{relative}: Lean exited with status {completed.returncode}")
        try:
            count = validate_output(expected, completed.stdout + "\n" + completed.stderr)
        except AuditError as error:
            raise AuditError(f"{relative}: {error}") from error
        total += count
        print(f"[axiom-audit] PASS {relative}: {count} reports", flush=True)
    print(f"[axiom-audit] PASS: {len(audits)} files, {total} reports; "
          f"allowed axioms: {', '.join(sorted(ALLOWED_AXIOMS))}", flush=True)


class ParserTests(unittest.TestCase):
    def test_multiline_and_no_axioms(self) -> None:
        output = """unrelated signature output
'Demo.one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Demo.two' does not depend on any axioms
"""
        self.assertEqual(validate_output(Counter({"Demo.one": 1, "Demo.two": 1}), output), 2)

    def test_location_prefix_ansi_and_prime_name(self) -> None:
        output = "\x1b[32mAudit.lean:4:0: info: 'Demo.one\'' depends on axioms: [propext]\x1b[0m\n"
        self.assertEqual(validate_output(Counter({"Demo.one'": 1}), output), 1)

    def test_source_comments_and_intentional_repetition(self) -> None:
        source = '''/- outer /- nested -/
#print axioms Hidden.block
-/
-- #print axioms Hidden.line
#eval "#print axioms Hidden.string"
#print axioms Demo.one -- trailing comment
#print axioms Demo.one
'''
        expected = expected_declarations(source)
        self.assertEqual(expected, Counter({"Demo.one": 2}))
        self.assertEqual(validate_output(expected,
            "'Demo.one' depends on axioms: [propext]\n" * 2), 2)

    def test_reject_invalid_outputs(self) -> None:
        cases = {
            "missing": "",
            "unexpected name": "'Demo.other' does not depend on any axioms\n",
            "extra duplicate": "'Demo.one' does not depend on any axioms\n" * 2,
            "sorry": "'Demo.one' depends on axioms: [propext, sorryAx]\n",
            "custom axiom": "'Demo.one' depends on axioms: [Demo.input]\n",
            "truncated": "'Demo.one' depends on axioms: [propext,\n",
            "empty item": "'Demo.one' depends on axioms: [propext,, Quot.sound]\n",
            "duplicate axiom": "'Demo.one' depends on axioms: [propext, propext]\n",
            "extra malformed report": (
                "'Demo.one' does not depend on any axioms\n"
                "'Demo.two' depends on axioms: [\n"
            ),
        }
        for label, output in cases.items():
            with self.subTest(label=label), self.assertRaises(AuditError):
                validate_output(Counter({"Demo.one": 1}), output)

    def test_reject_missing_intentional_repetition(self) -> None:
        with self.assertRaises(AuditError):
            validate_output(Counter({"Demo.one": 2}),
                "'Demo.one' does not depend on any axioms\n")

    def test_reject_empty_or_unsupported_source(self) -> None:
        for source in ("import Mathlib\n", "#print axioms\n", "#print axioms Demo.one Demo.two\n"):
            with self.subTest(source=source), self.assertRaises(AuditError):
                expected_declarations(source)

    def test_reject_unterminated_comment(self) -> None:
        with self.assertRaises(AuditError):
            expected_declarations("/- #print axioms Demo.one\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true", help="test parsers without invoking Lean")
    args = parser.parse_args()
    if args.self_test:
        result = unittest.TextTestRunner(verbosity=2).run(
            unittest.defaultTestLoader.loadTestsFromTestCase(ParserTests)
        )
        return 0 if result.wasSuccessful() else 1
    try:
        run_audits(Path(__file__).resolve().parent.parent)
    except (AuditError, OSError, UnicodeError) as error:
        print(f"[axiom-audit] FAIL: {error}", file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

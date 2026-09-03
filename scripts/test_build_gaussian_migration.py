"""Protocol tests only: these mocks do not compile or certify Lean proofs."""
import contextlib
import io
from pathlib import Path
import subprocess
import unittest
from unittest.mock import MagicMock, patch

import build_gaussian_migration as driver


class BatchProtocolTests(unittest.TestCase):
    def run_case(self, cached=(), fail=()):
        modules = {}
        for name, imports in {"Base": "", "Middle": "import Base",
                              "Leaf": "import Middle"}.items():
            path = MagicMock(spec=Path)
            path.read_text.return_value = imports
            modules[name] = path
        built, rejected, calls = set(cached), set(fail), []

        def run(command, **kwargs):
            calls.append(command)
            names = [word[1:] for word in command if word.startswith("+")]
            if "--no-build" in command:
                return subprocess.CompletedProcess(command, 0 if set(names) <= built else 1)
            if names:
                self.assertEqual(len(names), 1, "Compilation must remain serial")
                if names[0] in rejected:
                    return subprocess.CompletedProcess(command, 1)
                built.add(names[0])
            return subprocess.CompletedProcess(command, 0)

        with patch.object(driver, "TARGETS", {"root": ["Leaf"]}), \
             patch.object(driver, "sources", return_value=modules), \
             patch.object(driver.subprocess, "run", side_effect=run), \
             patch("sys.argv", ["build_gaussian_migration.py", "--project", "root"]), \
             contextlib.redirect_stdout(io.StringIO()):
            result = driver.main()
        return result, calls

    def test_cached_batch_still_gets_normal_final_build(self):
        result, calls = self.run_case(cached=["Base", "Middle", "Leaf"])
        self.assertEqual(result, 0)
        self.assertEqual(calls[-1], ["lake", "--no-cache", "build", "Leaf"])
        self.assertEqual(len(calls), 2)

    def test_cache_misses_compile_in_dependency_order(self):
        result, calls = self.run_case()
        self.assertEqual(result, 0)
        compiled = [call[-1] for call in calls
                    if "--no-build" not in call and call[-1].startswith("+")]
        self.assertEqual(compiled, ["+Base", "+Middle", "+Leaf"])

    def test_failed_dependency_blocks_descendants_and_final_build(self):
        result, calls = self.run_case(fail=["Base"])
        self.assertEqual(result, 1)
        self.assertFalse(any("--no-cache" in call for call in calls))
        compiled = [call[-1] for call in calls
                    if "--no-build" not in call and call[-1].startswith("+")]
        self.assertEqual(compiled, ["+Base"])


if __name__ == "__main__":
    unittest.main()

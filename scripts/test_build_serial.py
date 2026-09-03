"""Read-only regression tests: mock Lake; never run a local Lean process."""

from pathlib import Path
import subprocess
import unittest
from unittest.mock import call, patch

from build_serial import build_if_all_cached


class CachedFastPathTests(unittest.TestCase):
    def setUp(self):
        self.root = Path("/example/repository")
        self.order = ["Base.One", "Base.Two", "Final"]

    @patch("build_serial.subprocess.run")
    def test_miss_does_not_start_parallel_rebuild(self, run):
        run.return_value = subprocess.CompletedProcess([], 1)
        self.assertFalse(build_if_all_cached(self.root, self.order))
        run.assert_called_once_with(
            ["lake", "--no-build", "build", *self.order], cwd=self.root, check=False)

    @patch("build_serial.subprocess.run")
    def test_hit_normally_validates_every_module(self, run):
        run.return_value = subprocess.CompletedProcess([], 0)
        self.assertTrue(build_if_all_cached(self.root, self.order))
        self.assertEqual(run.call_args_list, [
            call(["lake", "--no-build", "build", *self.order], cwd=self.root, check=False),
            call(["lake", "build", *self.order], cwd=self.root, check=True),
        ])

    @patch("build_serial.subprocess.run")
    def test_normal_build_failure_is_not_swallowed(self, run):
        run.side_effect = [subprocess.CompletedProcess([], 0),
                           subprocess.CalledProcessError(1, ["lake", "build"])]
        with self.assertRaises(subprocess.CalledProcessError):
            build_if_all_cached(self.root, self.order)


if __name__ == "__main__":
    unittest.main()

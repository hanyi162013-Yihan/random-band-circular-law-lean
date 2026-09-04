"""Replay-log validation tests; they do not invoke Lean or certify a proof."""
import unittest
from replay_gaussian_migration import validate_replay


class KernelReplayProtocolTests(unittest.TestCase):
    def test_complete_success(self):
        self.assertEqual(validate_replay(["A", "B"], "replaying B\nreplaying A\n", 0), 2)

    def test_coverage_is_not_success_when_checker_fails(self):
        with self.assertRaises(RuntimeError):
            validate_replay(["A"], "replaying A\n", 1)

    def test_missing_duplicate_extra_and_empty_are_rejected(self):
        for targets, output in [(["A", "B"], "replaying A\n"),
                                (["A"], "replaying A\nreplaying A\n"),
                                (["A"], "replaying A\nreplaying B\n"), ([], "")]:
            with self.subTest(targets=targets, output=output), self.assertRaises(RuntimeError):
                validate_replay(targets, output, 0)


if __name__ == "__main__":
    unittest.main()

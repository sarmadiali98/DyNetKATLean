import argparse
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock

from v11_campaign import GROUPS, positive_timeout, wait_for_process
from v11_reference_timing import SCALES, recovery_selection, recorded_attempts, retry_metadata, run_timed


class TimeoutTests(unittest.TestCase):
    def test_omitted_timeout(self):
        child = Mock()
        wait_for_process(child, None)
        child.wait.assert_called_once_with(timeout=None)
        parser = argparse.ArgumentParser()
        parser.add_argument("--timeout", type=positive_timeout)
        self.assertIsNone(parser.parse_args([]).timeout)

    def test_completes_with_explicit_timeout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            row = run_timed([sys.executable, "-c", "pass"], root, None, root / "ok", 5)
        self.assertEqual(row["exit"], 0)
        self.assertEqual(row["timeout_seconds"], 5)

    def test_exceeds_explicit_timeout(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            row = run_timed([sys.executable, "-c", "import time; time.sleep(30)"],
                            root, None, root / "slow", 1)
        self.assertIsNone(row["exit"])
        self.assertEqual(row["status"], "timeout")
        self.assertGreaterEqual(row["wall_seconds"], 1)
        self.assertLess(row["wall_seconds"], 10)

    def test_invalid_timeouts(self):
        for script in ("v11_campaign.py", "v11_reference_timing.py"):
            arguments = (["--runtime", ".", "--results", "."] if "reference" in script else
                         ["--corpus", ".", "--lean", ".", "--output", "."])
            for value in ("0", "-1", "bad"):
                with self.subTest(script=script, value=value):
                    proc = subprocess.run([sys.executable, str(Path(__file__).with_name(script)),
                                           *arguments, "--timeout", value], capture_output=True, text=True)
                    self.assertEqual(proc.returncode, 2)
                    self.assertIn("timeout must be a positive integer", proc.stderr)

    def test_recovery_links_and_resume(self):
        rows = [
            dict(pods=n, group=g, mode=m, repeat=r, log=f"{n}-{g}-{m}-{r:02d}",
                 status="timeout" if (n >= 14 and m == "fresh") or
                 (n == 16 and g == "all_properties") else "completed", timeout_seconds=300)
            for r in range(1, 11) for n in SCALES for g in GROUPS for m in ("fresh", "reused")
        ]
        selected = recovery_selection(rows)
        self.assertEqual(len(selected), 90)
        key, source = next(iter(selected.items()))
        retry = dict(source, **retry_metadata(source))
        retry.update(log="retry-" + source["log"], status="completed", timeout_seconds=None)
        done = recorded_attempts([retry], selected)
        self.assertEqual(done, {key})
        self.assertEqual(len(selected.keys() - done), 89)
        self.assertEqual(source["status"], "timeout")
        self.assertEqual(retry["retry_of"], source["log"])
        with self.assertRaises(ValueError):
            recorded_attempts([retry, retry], selected)
        with self.assertRaises(ValueError):
            recorded_attempts([dict(retry, retry_of="wrong")], selected)


if __name__ == "__main__":
    unittest.main()

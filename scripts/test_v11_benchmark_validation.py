import json
from pathlib import Path
import tempfile
import unittest

from v11_benchmark_validation import interval_union, summarize_trace, time_metrics, verdicts


class BenchmarkValidationTests(unittest.TestCase):
    def test_gnu_elapsed_minutes_and_io(self):
        report = """Elapsed (wall clock) time (h:mm:ss or m:ss): 1:02:03.45
        User time (seconds): 12.50
        System time (seconds): 3
        Maximum resident set size (kbytes): 100
        File system inputs: 44
        File system outputs: 55
        Voluntary context switches: 66
        Involuntary context switches: 77"""
        result = time_metrics(report)
        self.assertEqual(result["elapsed_seconds"], 3723.45)
        self.assertEqual(result["max_rss_kib"], 100)
        self.assertEqual(result["fs_outputs"], 55)

    def test_overlapping_child_intervals_are_not_double_counted(self):
        self.assertEqual(interval_union([(0, 4), (2, 5), (7, 9), (8, 8.5)]), 7)
        self.assertEqual(interval_union([]), 0)

    def test_trace_classifies_subprocess_and_counts_worker(self):
        events = [
            dict(event="call", function="run", source="/lib/multiprocessing/process.py"),
            dict(event="call", function="netkat_process", source="/ref/src/python/preprocess.py"),
            dict(event="subprocess.Popen", executable="/bin/katbv"),
            dict(event="return", function="_execute_child", source="/lib/subprocess.py", child_pid=31),
            dict(event="return", function="run", source="/lib/subprocess.py"),
        ]
        with tempfile.TemporaryDirectory() as directory:
            trace = Path(directory) / "audit.jsonl"
            trace.write_text("".join(json.dumps(dict(event, monotonic=index, pid=20, ppid=10)) + "\n"
                                     for index, event in enumerate(events)))
            summary = summarize_trace(trace)
        self.assertEqual(summary["workers"], {20: 10})
        self.assertEqual(summary["invocation_counts"], {"preprocess/katbv": 1})
        self.assertEqual(summary["spans"][0]["pid"], 31)
        self.assertEqual(summary["spans"][0]["elapsed"], 2)

    def test_reference_missing_and_duplicate_verdicts_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "stdout"
            query = {"packet": "0", "index": 0, "polarity": "=0"}
            path.write_text("")
            with self.assertRaisesRegex(ValueError, "incomplete"):
                verdicts(path, [query], 0, "reference")
            line = "Packet: 0 - property: #0: property satisfied.\n"
            path.write_text(line)
            self.assertEqual(verdicts(path, [query], 0, "reference"), [False])
            path.write_text(line * 2)
            with self.assertRaisesRegex(ValueError, "duplicate"):
                verdicts(path, [query], 0, "reference")


if __name__ == "__main__":
    unittest.main()

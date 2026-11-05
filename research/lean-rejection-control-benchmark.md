# Lean rejection-control benchmark — 2026-11-05

Harness performance measurement, not a mathematical claim or a new theorem
certificate. Both complete localization runs passed the 137-statement positive
Comparator check, all 22 unfinished-proof controls, the combined project build,
complete axiom audit and selected regression suites. The parallel run also passed
the new pool regression suite.

| Measurement | Archived serial run | Four-worker run |
|---|---:|---:|
| Total recorded wall time | 43.52 min | 16.10 min |
| Rejection-control execution | 37.80 min | 10.16 min |
| Worker preparation | — | 10.88 s |
| Whole pool, including setup/cleanup | — | 10.36 min |
| Maximum active controls | 1 | 4 |
| Sampled aggregate worker RSS peak | not recorded | 31.75 GiB |
| Largest sampled individual worker RSS peak | not recorded | 8.15 GiB |

The observed total speedup is **2.70×**; control execution alone improved by
**3.72×**. These are single-run measurements on the same host with existing build
caches, not a universal performance guarantee. Total wall time is the difference
between manifest start and finish timestamps, excluding the final archive copy.
Serial control execution is the sum of its control command durations; parallel
execution is the pool's wall time, not the sum of overlapping command durations.

The host exposes 32 CPUs in its affinity mask and 60.42 GiB RAM. The four workers'
sampled peaks were 8.139, 8.151, 8.039 and 8.141 GiB. RSS is sampled every 0.5 seconds
and shared pages can be counted more than once; it is neither exact simultaneous
physical memory usage nor a guaranteed peak bound. Conservatively extrapolating
eight times the largest worker gives **65.21 GiB**, exceeding installed RAM.
Consequently the planned eight-worker benchmark was **not run**. Four remains the
default; `--control-jobs 1` restores serial execution without copying build trees.

## Provenance and scope checks

- [Serial manifest](../artifacts/certificates/lean/02195e4d735c016170afadaae421b25315b95dbff7a4eeefceb18800c7549ef1/manifest.json)
- [Four-worker manifest](../artifacts/certificates/lean/5a0bc761ec42592c948857ecac4bfb05f0f7d85394f90ae8b2ebb74fd5c95209/manifest.json)

The manifests' complete `lean/` source/configuration hash maps match. The ordered
22 control names and JSON configuration paths also match. Every recorded command
in the parallel run passed; its manifest confirms four active workers and scratch
cleanup. Individual logs, timestamps, worker assignments, memory samples' maxima,
copy-space preflight and setup/execution durations are archived with that manifest.

Command used for the parallel measurement:

```bash
python3 -B scripts/reproduce_lean.py --reuse-dependencies --triple-kernel-localization-only --control-jobs 4
```

The archived manifest identifies the precise source snapshot used for timing.
After this measurement, process-group cleanup was tightened to retire completed
group IDs immediately, avoiding retaining IDs that the OS could later reuse.
The six real-subprocess pool tests and twelve harness tests were rerun for that
cleanup change; the timing above remains the archived pre-refinement measurement.
No mathematical sources, theorem statuses, tool pins or sandbox permissions were
changed by this maintenance task.

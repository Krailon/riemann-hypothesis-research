# Work Package B reproduction harness

Task: verification and exposition. Assumptions: `UNCONDITIONAL` for exact
algebra, with `SUPPORT(h<=1-kappa, 0<kappa<1)` for the theorem.
Root: **TRIPLE-SMOOTHED-CORRELATION-001**, status **proved-draft**.

## Run and prerequisites

Use installed Python **3.12** (standard library only), Git and Bash.
Full mode also requires `pdflatex` with `geometry`, `amsmath`, `amssymb`,
`amsthm`, `booktabs`, `longtable`, `hyperref`, and their dependencies.
No BibTeX step is needed. Python and TeX versions are recorded, not
provisioned or locked. There are no downloads or dependency installations.

```bash
./scripts/reproduce_triple.sh --require-clean
./scripts/reproduce_triple.sh --checks-only
./scripts/reproduce_triple.sh --output-dir /tmp/triple-reproduction
```

The [entry point](../scripts/reproduce_triple.sh) works from another
working directory when invoked by path. Relative output paths resolve
against that calling directory. Default outputs use a unique ignored
`artifacts/reproduction/run-*` directory. Inside the repository, output
must be below `artifacts/reproduction/`; external destinations are allowed.
An existing nonempty destination is rejected without overwriting it.

`--require-clean` rejects tracked or untracked source changes. Without
it, development runs are allowed and record their dirty state. Both
modes recheck Git revision, status and source hashes before success.
A clean-checkout claim needs a fresh checkout and a manifest with
`dirty: false`; the flag alone does not create a fresh checkout.

## Workflow and artifacts

The [runner](../scripts/reproduce_triple.py) validates the recorded graph
and both RH audits, runs the pair and triple suites, generates exact
artifacts, and optionally builds the manuscript. Stale records stop the
run; audit hashes are never refreshed automatically. The pair runner
is unchanged; shared logging, hashing, output protection and TeX diagnostic
helpers retain their existing behavior.

| Output | Contents |
| --- | --- |
| `triple-normalization.json` | Exact boundary moments, six-sector ray incidences, normalization by `2/3`, five sine partitions and Fourier contributions, support and full-zero conventions, named error expansions and source labels. |
| `triple-normalization.md` | Readable rendering of the same mathematical record. |
| `triple_explicit_formula.pdf` | Triple manuscript compiled in three passes with shell escape disabled; full mode only. |
| `manifest.json` | Source revision and dirty state, input/output SHA256 hashes, Python/TeX versions, commands, stage outcomes, separate suite totals, graph/audit summaries and PDF diagnostics. |
| `logs/`, `build/` | Retained command logs and isolated TeX intermediates. |

The [generator](../scripts/triple_normalization.py) uses exact rational
arithmetic. Exponential integral identities and analytic error estimates
are inputs from the written proof. It derives the quadrant coefficients
`1/4` and `3/4`, the native signed coefficients `3/2`, their normalization
to one, and the observable coefficient `16/(3T log T)`.

Both `E_signed` and `E_kernel` retain their test and smoothing norms,
positive support margin and separate origins. Exact scaling multiplies
each inherited bound by `2/3`; the theorem absorbs this and the inherited
unspecified constants into its unspecified effective absolute constant.
No numerical value of that constant is computed. The critical parameter
specialization retains the finite-height factors `3b/(2q)` and `b/q`,
separately from their limits. Applying that specialization to all zeros
would require RH and is not part of the unconditional reproduction.

The [new tests](../scripts/check_triple_reproduction.py) independently
check finite coefficients, errors and failure behavior. They mock nested
suite execution to avoid recursive test discovery. Existing tests still
check the 27 words, 208 remainder refinements, kernel algebra, support,
multiplicity and complex arguments. No synthetic zero fixture is evidence
about the horizontal locations of actual zeta zeros.

## Outcomes and reproducibility limits

Full success reports `status: pass`. Explicit checks-only success reports
`status: partial` and `pdf.status: skipped`. Both return zero. Failure
returns nonzero and preserves a manifest and available logs once the
output directory exists. A missing TeX installation in full mode is an
error. Failed or skipped tests, discovery below the baseline counts of
70 pair/96 triple checks, stale audits, changed inputs, failed TeX,
unresolved references/citations and remaining rerun requests fail the run.
Other TeX warnings are recorded. The current suites contain 70 pair and
109 triple tests, including 13 new reproduction checks.

Mathematical JSON and Markdown outputs are deterministic. Paths, timestamps,
tool versions and PDF bytes may vary. The manifest records actual output
hashes and excludes itself; source hashing includes new source files but
excludes generated archives and session transcripts, using the pair
harness's source-file scope. No prior build outputs are used.

This is finite regression and regeneration from proved-draft analytic
inputs, not an analytic proof certificate, independent mathematical
verification, replay of external computational proofs, or a theorem-status
upgrade. Broader environment provisioning and CI remain deferred.
The existing hash-bound audit documents retain their historical scope.
A final Work Package B baseline selection, durable artifact archive and
closure review are separate from implementing and exercising this harness.

## Validation evidence

Validation completed on **2026-10-03**. The full development run
passed, and the checks-only run reported `partial` with a skipped PDF.
Their deterministic JSON and Markdown agree byte for byte with the clean
clone's outputs.

A temporary repository was cloned locally from parent revision
`a850e7d5ff06336e51df86864e705da24e80e439`. The implementation source files
were copied into that repository, checked against the working source hashes,
and committed there as snapshot
`f36168156c0851b82b2372607ccc68ec382af4b6`. A second fresh clone of this
snapshot ran the full command from outside the repository, using paths
containing a space. No commit was made in the user's working repository.

| Evidence | Result |
| --- | --- |
| Mode / outcome | `full` / `pass`, with `--require-clean` |
| Source state | `dirty: false`, empty Git status at start and finish |
| Pair suite | 70 passed, no failures, errors or skips |
| Triple suite | 109 passed, including 13 reproduction tests; no failures, errors or skips |
| Graph / audits | Existing graph and both audit records validated without modification |
| PDF | 34 pages, three passes, no final-pass warnings or unresolved references |
| Output integrity | All 19 manifest-listed output hashes verified |
| Formula determinism | JSON and Markdown identical across full development, checks-only and clean-clone runs |
| Manifest SHA256 | `46cab19012617f8f6239df9feaad97cf36d0218c7daa6b870e2653ce4d79bea3` |

Temporary clean-run manifest:
`/tmp/triple-clean-checkout-saz6hdxl/bundle/manifest.json`.
Development bundles: `artifacts/reproduction/run-4h0rvqwr/` (full) and
`artifacts/reproduction/run-y7inaqfw/` (checks-only).
These paths are temporary or ignored development evidence, not a durable
Work Package B baseline archive.

This evidence applies to the temporary snapshot, not the unchanged parent
commit or a future final baseline. The snapshot contains the instructions
above; this validation-evidence section was appended after the run. All
other source inputs match the tested snapshot. The proof, theorem ledger,
audit records and their hash-bound sources were not changed by this task.

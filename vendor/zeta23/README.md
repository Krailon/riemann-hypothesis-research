# Selected Zeta23 sources

Source: https://github.com/anthropics/formal-math, commit
`e1a4e6508154ea59f030480661590a9fe3018011`, `zeta23/`.
Copyright 2026 Anthropic, PBC; Apache 2.0. See LICENSE and NOTICE.

`upstream/` contains immutable originals of the 45-module closure of
`Zeta23.LinAlg.RankTrace`, `Zeta23.RvM.Statement`, and
`Zeta23.GammaFacts.Complete`. The root metadata files are upstream originals.
The active, modified port lives in `lean/Zeta23/`.

`manifest.json` records the pin and hashes; `compatibility.patch` is the exact
original-to-port diff, including forwarding modules for existing PNT dependencies.
Run `python3 -B scripts/check_zeta23_import.py` to verify provenance.
For mathematical scope and dependency substitutions, see
[the audit](../../research/lean-zeta23.md).

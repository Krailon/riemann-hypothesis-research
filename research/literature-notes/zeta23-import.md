# Zeta23 selected proof import

Assumptions: `UNCONDITIONAL`. Source type: **software**, not a journal-paper citation.
Bibliography key: `Zeta23FormalMath2026`.

Exact pin, license, dependency audit, conventions and verification scope:
[lean-zeta23.md](../lean-zeta23.md).

Imported lemmas: `RHLinalg.rank_trace_ineq`, `rank_trace_ineq_two`, and
`Zeta23.RvM.riemannVonMangoldt` instantiated with `Zeta23.gammaFacts`.
The last theorem gives dyadic `(T,2T]` counts and local upper counts, with analytic
multiplicity. Project adapters prove the closed-endpoint correction explicitly.
No Fourier normalization translation is needed for these statements.

The selected source contains no result identified as proving our signed
complex-argument error tends to zero. Rank--trace is useful for future horizontal
extraction; the count theorem strengthens the formalized analytic foundation.
Neither supplies a conventional ordinate-only triple asymptotic on its own.

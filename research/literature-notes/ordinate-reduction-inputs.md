# Primary inputs for the ordinate reduction

Reviewed 2026-10-03. Task: stated-hypothesis and application review.
Assumptions: `UNCONDITIONAL`. Full upstream reconstruction and independent
project review have not been performed.

## GLSS: close-pair count

[Goldston, Lee, Schettler and Suriajaya, arXiv:2503.15449v4](https://arxiv.org/abs/2503.15449v4),
**PREPRINT**, version dated 30 March 2026. Consulted the versioned
[full text](https://arxiv.org/html/2503.15449v4), Sections 3, 5 and 6.

Import only equation (6.1)'s upper-bound consequence for
`1<=lambda<=sqrt(log V/(2pi))`: the nonnegative triangular pair sum is
`O(V log V lambda)`. This source derives (6.1) from its unconditional
Propositions 1 and 2. Fujii/Tsang/Selberg are upstream inputs, not original
texts inspected in this review. The PCC-dependent main theorem and the
RH-dependent refinement in Remark 2 are unused.

The sum counts all ordered occurrences with `0<gamma,gamma_prime<=V`,
including equal ordinates. Source scale is `log V/(2pi)`, not project
`log(T/(2pi))/(2pi)`. Use `V=3T`, `lambda=2R L_(3T)/L_T`;
the desired close pairs have weight at least 1/2. The range is checked
uniformly up to `R=(log T)^(1/4)`. No explicit constant is extracted.

## Simonic: density near the line

[Simonic, author text arXiv:1910.08274v2](https://arxiv.org/pdf/1910.08274v2),
Theorem 1, p. 2; definition of `N(sigma,T)` on p. 1; proof Section 4.5.
Published metadata: J. Math. Anal. Appl. 491 (2020), article 124303,
[DOI](https://doi.org/10.1016/j.jmaa.2020.124303).
The consulted author text is not claimed to be a checked journal-text match.

Import the uniform consequence
`N(1/2+D,2V)-N(1/2+D,V)<<V^(1-D/4)log V+log^2 V`
for `0<=D<=0.331`, `V>=3.0610046*10^10`.
The count uses strict `beta>sigma`, positive ordinate `<=V`, multiplicity.
External finite-height/numerical provenance is inherited; this project
neither replays it nor uses it to substitute critical-line locations.

Use three dyadic windows covering `[T-1,2T+1]`, reflect the left half-strip,
and set `D=64 log log T/log T`. All application heights eventually exceed
the source threshold. This controls the real-test kernel error; it provides
no vanishing bound for the required moment of `(beta-1/2)log T`.

### Reuse in the signed cancellation budget

No additional source theorem is imported. The same dyadic density estimate
is applied with `D=v/log T` up to its stated endpoint `331/1000`; at larger
v monotonicity retains the endpoint bound. The weighted triple tail has
factor `exp(-v/4)`. This yields the explicitly restricted kernel-mixing
result `h<=s<331/4000`, using the new local `q^-2` gain. The density estimate
is applied only to comparable heights; remote partners are separately
bounded. It still gives no vanishing bound for the even hyperbolic term.

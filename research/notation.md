# Project notation

Task type: exposition. Assumptions: `UNCONDITIONAL`.
These conventions implement AGENTS.md §2; they assert no correlation theorem.

- A nontrivial zero is \(\rho=\beta+i\gamma\), with
  \(\delta_\rho=\beta-1/2\). Zeros are counted with multiplicity.
- The symmetries are \(\rho\mapsto1-\rho\) and
  \(\rho\mapsto\bar\rho\). Their composition
  \(\rho\mapsto1-\bar\rho\) preserves a positive ordinate and multiplicity.
- For \(T>2\pi\), use
  \(L_T=\log(T/2\pi)/(2\pi)\),
  \(u_{jk}=L_T(\gamma_k-\gamma_j)\), and
  \(x_\rho=(\beta-1/2)\log T\).
- The Fourier convention is
  \[
  \widehat f(\xi)=\int_{\mathbb R}f(u)e^{-2\pi i u\xi}\,du,
  \qquad f(u)=\int_{\mathbb R}\widehat f(\xi)e^{2\pi i u\xi}\,d\xi,
  \]
  with the dot product in higher dimensions and hypotheses specified at use.
- \(I_T\) indexes all zero occurrences with \(0<\gamma\leq T\);
  \(N(T)=|I_T|\). Distinct indices can represent the same complex zero.
  \(\mathcal Z_T\) is the set of distinct complex zeros in that range;
  \(m(z)\) is the multiplicity of \(z\in\mathcal Z_T\).
- Every tuple sum specifies its index set. The conditions \(j=k\),
  \(\rho_j=\rho_k\), and \(\gamma_j=\gamma_k\) are different diagonal
  conventions; none is implicit in a distinctness assertion.
- For the pair baseline only, set
  \(A_T=\log T/(2\pi)\), \(C_T=TA_T\), and
  \(q_T=A_T/L_T\). Keep \(C_T\), \(TL_T\), and \(N(T)\) distinct.
  Use \(X>0\) for the source's exponential base to avoid conflict with
  \(x_\rho\); use \(\Phi(X,T)\) and \(\mathcal F_T(\alpha)\) for its
  unnormalized and normalized pair sums.

The imported pair theorem permits \(T\geq3\). Translations involving
\(L_T^{-1}\) in this project use \(T>2\pi\).

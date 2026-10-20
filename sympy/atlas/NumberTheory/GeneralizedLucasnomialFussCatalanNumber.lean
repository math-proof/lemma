/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedLucasnomialFussCatalanNumber.lean -/

import sympy.atlas.NumberTheory.LucasPolytopicNumber
namespace MetaMathlibExt

/-- Generalized Lucasnomial Fuss-Catalan number after Ballot, JIS Vol. 21:
`C_{U,a,r}(n) = (U_r / U_{(a-1)*n+r}) * binom{a*n+r-1}{n}_U`,
for `a >= 2`, `r >= 1`, `n >= 1`, over a parameterized Lucas sequence `U`.
Totalized over all naturals; bounds are documented, not enforced.
Concept `jis_sem_17c3c7bf3e94f23255e5a2a1`;
source SHA-256 `ca51d34e717a237b02bca4bfa28c57dfc15c81f1276c7634d5abe998d1c48b89`. -/
noncomputable def generalizedLucasnomialFussCatalan
    (P : LucasParameters) (a r n : ℕ) : ℝ :=
  (lucasBracket P r / lucasBracket P ((a - 1) * n + r)) *
    lucasnomial P (a * n + r - 1) n

/-- Same family under the Ballot, JIS Vol. 24 parameter names:
`C_{U,r,s}(t) = (U_s / U_{(r-1)*t+s}) * binom{r*t+s-1}{t}_U`,
for `r >= 2`, `s >= 1`, `t >= 1`.
Concept `jis_sem_17c3c7bf3e94f23255e5a2a1`;
source SHA-256 `de2518f50026ac96429ae9113e738d224b1c1b732eec121bd4da5e8d60207f1c`. -/
noncomputable def generalizedLucasnomialFussCatalanRS
    (P : LucasParameters) (r s t : ℕ) : ℝ :=
  (lucasBracket P s / lucasBracket P ((r - 1) * t + s)) *
    lucasnomial P (r * t + s - 1) t

/-- The Vol. 21 `(a, r, n)` and Vol. 24 `(r, s, t)` parameterizations agree
under the renaming `r := a`, `s := r`, `t := n`; they are the same function.
Concept `jis_sem_17c3c7bf3e94f23255e5a2a1`. -/
theorem generalizedLucasnomialFussCatalan_vol24_eq
    (P : LucasParameters) (a r n : ℕ) :
    generalizedLucasnomialFussCatalan P a r n =
      generalizedLucasnomialFussCatalanRS P a r n := rfl

end MetaMathlibExt

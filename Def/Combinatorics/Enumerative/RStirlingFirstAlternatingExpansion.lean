/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RStirlingFirstAlternatingExpansion.lean -/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Tactic.LinearCombination
/-! Broder's expansion formula for r-Stirling numbers of the first kind.

Source: A. Z. Broder, "The r-Stirling numbers",
Stanford Computer Science Report STAN-CS-82-949 (December 1982),
PDF page 16 / printed page 13, Equation (43);
later published in Discrete Mathematics 49 (1984), 241-259,
DOI 10.1016/0012-365X(84)90161-4.

Equation (24) (PDF page 12 / printed page 9):
  ∑ k, [n,k]_r z^k = z^r (z+r)(z+r+1)...(z+n-1), n ≥ r > 0.
Equation (43): (-1)^r [n,m]_r = ∑ k, [n,m-r+k] {k-1,r-1} (-1)^k, n ≥ r ≥ 1.
-/


namespace MetaMathlibExt

/-- Unsigned r-Stirling number of the first kind, after A. Z. Broder,
"The r-Stirling numbers", Stanford Computer Science Report STAN-CS-82-949
(December 1982), PDF page 12 / printed page 9, Equation (24);
journal version: Discrete Mathematics 49 (1984), 241-259,
DOI 10.1016/0012-365X(84)90161-4.

Equation (24) characterizes `[n,m]_r` by
`∑ k, [n,k]_r z^k = z^r (z+r)(z+r+1)...(z+n-1)` for `n ≥ r > 0`.
The definition below is the coefficient of `X^m` in
`X^r * ∏ k in Finset.Ico r n, (X + C k)` over `Polynomial ℕ`,
which directly implements Equation (24), including zero outside the
triangular support. -/
noncomputable def rStirlingFirst (n m r : ℕ) : ℕ :=
  Polynomial.coeff
    ((Polynomial.X : Polynomial ℕ) ^ r *
      Finset.prod (Finset.Ico r n)
        (fun k => (Polynomial.X : Polynomial ℕ) + Polynomial.C k)) m

end MetaMathlibExt

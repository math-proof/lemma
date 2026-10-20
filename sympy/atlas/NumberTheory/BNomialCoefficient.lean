/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BNomialCoefficient.lean -/

import Mathlib.Algebra.Polynomial.Coeff

/-!
# Type-1 b-nomial coefficients

For a base `b ≥ 2`, the type-1 `b`-nomial coefficients are the coefficients of
`(1 + X + ⋯ + X ^ (b - 1)) ^ n`. The coefficient is defined to be zero at negative
integer indices.

Source: Ji Young Choi, *Digit Sums Generalizing Binomial Coefficients*,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Choi/choi15.tex>.

JIS concept: `jis_sem_aa36cef0f9c151f781c75a07`.
-/

open scoped BigOperators
open Polynomial

namespace MetaMathlibExt

/-- The polynomial `1 + X + ⋯ + X ^ (b - 1)` for a source-valid base `b ≥ 2`. -/
noncomputable def bNomialBase (b : ℕ) (_hb : 2 ≤ b) : Polynomial ℤ :=
  ∑ i ∈ Finset.range b, X ^ i

/-- The type-1 `b`-nomial coefficient in row `n` and integer-indexed column `k`.
It is zero for negative `k`. -/
noncomputable def bNomialCoefficient (b : ℕ) (hb : 2 ≤ b) (n : ℕ) (k : ℤ) : ℤ :=
  if k < 0 then 0 else ((bNomialBase b hb) ^ n).coeff k.toNat

end MetaMathlibExt

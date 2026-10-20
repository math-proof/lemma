/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GeneralizedFussCatalanNumbersFMNK.lean -/

import Mathlib.Data.Nat.Choose.Basic

/-!
# Generalized Fuss–Catalan numbers

This file defines the generalized Fuss–Catalan numbers, also called Raney numbers.

Provenance: JIS semantic concept `jis_sem_69c4f50c7aa0eee05d643c54`, statement
`jis_059ca809c2428bd341da0fee`, from
<https://cs.uwaterloo.ca/journals/JIS/VOL21/He/he61.tex>, SHA-256
`c73d8bdaba1725e18630db49af924a0cb5433b6b00878e556c2c9fdb7e2ae320`.
-/

namespace MetaMathlibExt

/-- The generalized Fuss–Catalan number `F_m(n, k)`:
`k * Nat.choose (m * n + k) n / (m * n + k)`.

The source considers `m ≥ 2` and `n, k ≥ 1`. The definition is totalized over natural numbers.
-/
def generalizedFussCatalanNumber (m n k : ℕ) : ℕ :=
  k * Nat.choose (m * n + k) n / (m * n + k)

/-- The defining equation for `generalizedFussCatalanNumber`. -/
theorem generalizedFussCatalanNumber_eq (m n k : ℕ) :
    generalizedFussCatalanNumber m n k =
      k * Nat.choose (m * n + k) n / (m * n + k) :=
  rfl

/-- The specialization `F_m(1, k) = k`, corresponding to case (c) of the source theorem. -/
theorem generalizedFussCatalanNumber_one (m k : ℕ) :
    generalizedFussCatalanNumber m 1 k = k := by
  unfold generalizedFussCatalanNumber
  have hmk : m * 1 + k = m + k := by omega
  rw [hmk, Nat.choose_one_right]
  by_cases h : m + k = 0
  · have hk : k = 0 := by omega
    simp [hk]
  · have hpos : 0 < m + k := by omega
    exact Nat.mul_div_cancel k hpos

end MetaMathlibExt

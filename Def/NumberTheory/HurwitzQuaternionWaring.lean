/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HurwitzQuaternionWaring.lean -/

module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

section

namespace MetaMathlibExt

/-- Hurwitz integrality predicate shared by all helpers. -/
def IsHurwitz (z : Quaternion ℚ) : Prop :=
  (∃ a b c d : ℤ,
    z.re = (a : ℚ) ∧ z.imI = (b : ℚ) ∧ z.imJ = (c : ℚ) ∧ z.imK = (d : ℚ)) ∨
  (∃ a b c d : ℤ,
    z.re = (a : ℚ) + 1 / 2 ∧ z.imI = (b : ℚ) + 1 / 2 ∧
      z.imJ = (c : ℚ) + 1 / 2 ∧ z.imK = (d : ℚ) + 1 / 2)

/-- The finite-difference sum `H ℓ t m = ∑_{j ≤ ℓ} (-1)^{ℓ-j} C(ℓ,j) (m+j)^t`. -/
def Hdiff (ℓ t : ℕ) (m : ℤ) : ℤ :=
  ∑ j ∈ Finset.range (ℓ + 1),
    (-1 : ℤ) ^ (ℓ - j) * ((ℓ.choose j : ℕ) : ℤ) * (m + (j : ℤ)) ^ t

end MetaMathlibExt
end

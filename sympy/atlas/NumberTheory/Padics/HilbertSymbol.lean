/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Padics/HilbertSymbol.lean -/

import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# The p-adic Hilbert symbol

This file defines the Hilbert symbol on nonzero p-adic numbers through solvability of the
associated binary quadratic equation.
-/

namespace HilbertSymbol

variable (F : Type*) [Field F]

/-- The equation `a * x ^ 2 + b * y ^ 2 = 1` is solvable over `F`. -/
def IsSolvable (a b : Fˣ) : Prop :=
  ∃ x y : F, (a : F) * x ^ 2 + (b : F) * y ^ 2 = 1

end HilbertSymbol

open Classical in
/-- The Hilbert symbol over a field, valued in `{1, -1}` according to whether the associated
binary quadratic equation is solvable. -/
noncomputable def hilbertSymbol (F : Type*) [Field F] (a b : Fˣ) : ℤ :=
  if HilbertSymbol.IsSolvable F a b then 1 else -1

namespace hilbertSymbol

variable {F : Type*} [Field F]

@[simp]
theorem eq_one_iff {a b : Fˣ} :
    hilbertSymbol F a b = 1 ↔ HilbertSymbol.IsSolvable F a b := by
  simp [hilbertSymbol]

theorem eq_neg_one_iff {a b : Fˣ} :
    hilbertSymbol F a b = -1 ↔ ¬HilbertSymbol.IsSolvable F a b := by
  simp [hilbertSymbol]

/-- The Hilbert symbol takes only the values one and negative one. -/
theorem eq_one_or_neg_one (a b : Fˣ) :
    hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 := by
  unfold hilbertSymbol
  split_ifs <;> simp

end hilbertSymbol

/-- The `p`-adic Hilbert symbol, defined by solvability of
`a * x ^ 2 + b * y ^ 2 = 1` over `ℚ_[p]`. -/
noncomputable def padicHilbertSymbol (p : ℕ) [Fact (Nat.Prime p)]
    (a b : ℚ_[p]ˣ) : ℤ :=
  hilbertSymbol ℚ_[p] a b

namespace padicHilbertSymbol

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The `p`-adic Hilbert symbol is one exactly when its defining equation is solvable. -/
@[simp]
theorem eq_one_iff {a b : ℚ_[p]ˣ} :
    padicHilbertSymbol p a b = 1 ↔
      ∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
  hilbertSymbol.eq_one_iff

/-- The `p`-adic Hilbert symbol is negative one exactly when its defining equation is not
solvable. -/
theorem eq_neg_one_iff {a b : ℚ_[p]ˣ} :
    padicHilbertSymbol p a b = -1 ↔
      ¬∃ x y : ℚ_[p], (a : ℚ_[p]) * x ^ 2 + (b : ℚ_[p]) * y ^ 2 = 1 :=
  hilbertSymbol.eq_neg_one_iff

/-- The `p`-adic Hilbert symbol takes only the values one and negative one. -/
theorem eq_one_or_neg_one (a b : ℚ_[p]ˣ) :
    padicHilbertSymbol p a b = 1 ∨ padicHilbertSymbol p a b = -1 :=
  hilbertSymbol.eq_one_or_neg_one a b

@[simp]
theorem sq (a b : ℚ_[p]ˣ) : padicHilbertSymbol p a b ^ 2 = 1 := by
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

theorem ne_zero (a b : ℚ_[p]ˣ) : padicHilbertSymbol p a b ≠ 0 := by
  rcases eq_one_or_neg_one a b with h | h <;> simp [h]

end padicHilbertSymbol

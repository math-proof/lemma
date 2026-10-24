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

end hilbertSymbol
/-- The `p`-adic Hilbert symbol, defined by solvability of
`a * x ^ 2 + b * y ^ 2 = 1` over `ℚ_[p]`. -/
noncomputable def padicHilbertSymbol (p : ℕ) [Fact (Nat.Prime p)]
    (a b : ℚ_[p]ˣ) : ℤ :=
  hilbertSymbol ℚ_[p] a b

namespace padicHilbertSymbol

variable {p : ℕ} [Fact (Nat.Prime p)]
end padicHilbertSymbol

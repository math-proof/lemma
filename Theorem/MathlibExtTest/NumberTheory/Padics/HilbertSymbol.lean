/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/HilbertSymbol.lean -/


import Def.NumberTheory.Padics.HilbertSymbol
import Lemma.Nat.Padics.HilbertSymbol
variable {F : Type*} [Field F]

/-!
# Tests for the Hilbert symbol

Examples exercising solvability and the public Hilbert symbol API.
-/


example (b : Fˣ) : HilbertSymbol.IsSolvable F (1 : Fˣ) b :=
  ⟨1, 0, by simp⟩

example (a : Fˣ) : HilbertSymbol.IsSolvable F a (1 : Fˣ) :=
  ⟨0, 1, by simp⟩

example (b : Fˣ) : hilbertSymbol F (1 : Fˣ) b = 1 := by
  rw [hilbertSymbol.eq_one_iff]
  exact ⟨1, 0, by simp⟩

example (a b : Fˣ) : hilbertSymbol F a b = 1 ∨ hilbertSymbol F a b = -1 :=
  hilbertSymbol.eq_one_or_neg_one a b

variable {p : Nat} [Fact (Nat.Prime p)]

example (b : ℚ_[p]ˣ) : padicHilbertSymbol p (1 : ℚ_[p]ˣ) b = 1 := by
  rw [padicHilbertSymbol.eq_one_iff]
  exact ⟨1, 0, by simp⟩

example (a b : ℚ_[p]ˣ) : padicHilbertSymbol p a b ^ 2 = 1 :=
  padicHilbertSymbol.sq a b

example (a b : ℚ_[p]ˣ) : padicHilbertSymbol p a b ≠ 0 :=
  padicHilbertSymbol.ne_zero a b


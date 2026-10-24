/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Padics/HilbertSymbol/Real.lean -/


import sympy.atlas.NumberTheory.Padics.HilbertSymbol.Real
import Lemma.Nat.Padics.HilbertSymbol.Real

/-!
# Tests for the real Hilbert symbol
-/

set_option autoImplicit false


/-- `realHilbertSymbol` unfolds to the generic symbol over `ℝ`. -/
example (a b : ℝˣ) : realHilbertSymbol a b = hilbertSymbol ℝ a b :=
  rfl

example : realHilbertSymbol (1 : ℝˣ) (1 : ℝˣ) = 1 := by
  rw [realHilbertSymbol.eq_one_iff]
  exact ⟨1, 0, by simp⟩

example : realHilbertSymbol (1 : ℝˣ) (-1 : ℝˣ) = 1 := by
  rw [realHilbertSymbol.eq_one_iff]
  exact ⟨1, 0, by simp⟩

example : realHilbertSymbol (-1 : ℝˣ) (1 : ℝˣ) = 1 := by
  rw [realHilbertSymbol.eq_one_iff]
  exact ⟨0, 1, by simp⟩

example : realHilbertSymbol (-1 : ℝˣ) (-1 : ℝˣ) = -1 :=
  realHilbertSymbol.eq_neg_one_iff_both_neg.mpr ⟨by simp, by simp⟩

example (a b : ℝˣ) (ha : (a : ℝ) < 0) (hb : (b : ℝ) < 0) :
    realHilbertSymbol a b = -1 :=
  realHilbertSymbol.eq_neg_one_iff_both_neg.mpr ⟨ha, hb⟩

example (a b : ℝˣ) (h : realHilbertSymbol a b = -1) :
    (a : ℝ) < 0 ∧ (b : ℝ) < 0 :=
  realHilbertSymbol.eq_neg_one_iff_both_neg.mp h

example (a b : ℝˣ) : realHilbertSymbol a b ^ 2 = 1 :=
  realHilbertSymbol.sq a b

example (a b : ℝˣ) : realHilbertSymbol a b ≠ 0 :=
  realHilbertSymbol.ne_zero a b

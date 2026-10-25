import Mathlib
import Theorem.Analysis.Appendix_A_7


abbrev NewInt.quot {X:Type} {f: ℤ → X} (hf: f 12 = f 2) : NewInt → X := by
  apply Quot.lift f
  intro a b
  simp [make_twelve_equal_two]
  intro ha hb
  rw [ha, hb, hf]


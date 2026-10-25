import Mathlib
import Def.Analysis.Appendix_A_7


abbrev make_twelve_equal_two : ℤ → ℤ → Prop := fun a b ↦ a = 12 ∧ b = 2

/-- A version of the integers where 12 has been forced to equal 2. -/
abbrev NewInt := Quot make_twelve_equal_two


/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GesselWord.lean -/


import sympy.atlas.NumberTheory.GesselWord
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

/-- The empty word over the empty alphabet is a Gessel word. -/
example : IsGesselWord 0 [] := by
  intro w' suffix _ k _ hkn
  omega

/-- The source's word `2, bar 1` is a Gessel word over `[2]`. -/
example : IsGesselWord 2 [Sum.inl (1 : Fin 2), Sum.inr (0 : Fin 2)] := by
  intro w' suffix h k hk1 hkn
  have hp := eq_nil_or_eq_singleton_or_eq_pair_of_append_eq_pair
    (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2)) w' suffix h
  rcases hp with rfl | rfl | rfl <;> interval_cases k <;> decide

/-- The source's word `1, bar 2` is not a Gessel word over `[2]`. -/
example : ¬ IsGesselWord 2 [Sum.inl (0 : Fin 2), Sum.inr (1 : Fin 2)] := by
  intro h
  have hbad := h [Sum.inl (0 : Fin 2), Sum.inr (1 : Fin 2)] [] (by simp) 1
    (by decide) (by decide)
  norm_num [gesselBalance, gesselUnbarredCount, gesselBarredCount] at hbad

end MetaMathlibExt

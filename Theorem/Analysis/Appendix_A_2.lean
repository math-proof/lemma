import Mathlib


/-!
# Analysis I, Appendix A.2: Implication

An introduction to implications.  Showcases some basic tactics and Lean syntax.

-/
theorem example_A_2_1 (x:ℤ) : x = 2 → x^2 = 4 := by
  intro h
  rw [h]
  rfl

theorem theorem_A_2_4 (n:ℤ) : Even (n * (n+1)) := by
  have : Even n ∨ Odd n := Int.even_or_odd n
  obtain heven | hodd := this  -- can also use `rcases this with heven | hodd`
  . exact Even.mul_right heven _
  have : Even (n+1) := Odd.add_one hodd
  exact Even.mul_left this _

theorem contrapositive {X Y: Prop} (hXY: X → Y) : ¬ Y → ¬ X := by
  intro hY
  by_contra hX
  have := hXY hX
  contradiction

theorem imp_example (x:ℝ) : (x = 2) → (x^2 = 4) := by
  intro h
  rw [h]
  norm_num

theorem imp_contrapositive (x:ℝ) : (x^2 ≠ 4) → (x ≠ 2) := by
  convert contrapositive (imp_example x)


import Mathlib
import Abbrev.Analysis.Section_9_2
/-!
# Analysis I, Section 9.2: The algebra of real-valued functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text.  When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where
the Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Recalling basic pointwise operations on functions.

-/


namespace Chapter9

/-- Definition 9.2.1 (Arithmetic operations on functions). -/
theorem add_func_eval (f g: ℝ → ℝ) (x: ℝ) : (f + g) x = f x + g x := rfl

theorem sub_func_eval (f g: ℝ → ℝ) (x: ℝ) : (f - g) x = f x - g x := rfl

theorem max_func_eval (f g: ℝ → ℝ) (x: ℝ) : max f g x = max (f x) (g x) := rfl

theorem min_func_eval (f g: ℝ → ℝ) (x: ℝ) : min f g x = min (f x) (g x) := rfl

theorem mul_func_eval (f g: ℝ → ℝ) (x: ℝ) : (f * g) x = f x * g x := rfl

theorem div_func_eval (f g: ℝ → ℝ) (x: ℝ) : (f / g) x = f x / g x := rfl

theorem smul_func_eval (c: ℝ) (f: ℝ → ℝ) (x: ℝ) : (c • f) x = c * f x := rfl

end Chapter9

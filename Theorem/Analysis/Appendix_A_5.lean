import Mathlib
/-!
# Analysis I, Appendix A.5: Nested quantifiers

Some examples of nested quantifiers in Lean

-/


namespace SwanExample

variable (Swans:Type)
variable (isBlack : Swans → Prop)
end SwanExample
theorem square_expand : ∀ (x:ℝ), (x + 1)^2 = x^2 + 2 * x + 1 := by
  intro x
  ring

theorem solve_quadratic : ∃ (x:ℝ), x^2 + 2 * x - 8 = 0 := by
  use 2
  norm_num

/- The following proof will not typecheck.

example : Real.pi^2 + 2 * Real.pi - 8 = 0 := by
  apply solve_quadratic

-/


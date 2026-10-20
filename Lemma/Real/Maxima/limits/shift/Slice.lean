import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {S : Set ℝ}
  (c : ℝ) :
-- imply
  Maxima S (fun x => f (x + c)) = Maxima ((fun x => x + c) '' S) f := by
-- proof
  rw [Maxima, Maxima, ← Set.image_comp]
  rfl


-- created on 2023-03-27
-- updated on 2026-10-17

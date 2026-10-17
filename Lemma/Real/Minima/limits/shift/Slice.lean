import sympy.concrete.expr_with_limits
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {S : Set ℝ}
  (c : ℝ) :
-- imply
  Minima S (fun x => f (x + c)) = Minima ((fun x => x + c) '' S) f := by
-- proof
  rw [Minima, Minima, ← Set.image_comp]
  rfl


-- created on 2026-10-11
-- updated on 2026-10-17

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import sympy.Basic


@[path]
private lemma main
  {f : ℝ → ℝ}
  {S : Set ℝ}
  (c : ℝ) :
-- imply
  sInf ((fun x => f (x + c)) '' S) = sInf (f '' ((fun x => x + c) '' S)) := by
-- proof
  rw [← Set.image_comp]
  rfl


-- created on 2026-10-11
-- updated on 2026-10-17

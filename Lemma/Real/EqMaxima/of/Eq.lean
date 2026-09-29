import sympy.Basic
import sympy.concrete.expr_with_limits
import Mathlib.Algebra.Order.Archimedean.Real.Basic


@[main]
private lemma main
  [SupSet β]
  {S : Set α}
  {f g : α → β}
-- given
  (h : ∀ i ∈ S, f i = g i) :
-- imply
  Maxima S f = Maxima S g := by
-- proof
  unfold Maxima
  rw [Set.image_congr h]


-- created on 2026-09-27

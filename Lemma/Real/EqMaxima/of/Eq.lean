import Initialize.Tactic.Attr.Basic
import Syntax.Order.ExprWithLimits
import Mathlib.Algebra.Order.Archimedean.Real.Basic


@[path]
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


-- created on 2019-04-08

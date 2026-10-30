import Initialize.Tactic.Attr.Basic
import Syntax.Order.ExprWithLimits


@[path]
private lemma main
  [Nonempty α] [Preorder β]
  {f g : α → β}
-- given
  (h : f = g) :
-- imply
  max⁻¹ Set.univ f = max⁻¹ Set.univ g := by
-- proof
  rw [h]


-- created on 2021-12-17

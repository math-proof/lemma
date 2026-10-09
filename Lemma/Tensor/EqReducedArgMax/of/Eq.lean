import sympy.Basic
import sympy.concrete.expr_with_limits


@[path]
private lemma main
  [Nonempty α] [Preorder β]
  {f g : α → β}
-- given
  (h : f = g) :
-- imply
  ArgMax Set.univ f = ArgMax Set.univ g := by
-- proof
  rw [h]


-- created on 2021-12-17

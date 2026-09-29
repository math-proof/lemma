import sympy.Basic
import sympy.concrete.expr_with_limits


@[main]
private lemma main
  [Nonempty α] [Preorder β]
  {f g : α → β}
-- given
  (h : f = g) :
-- imply
  ArgMax Set.univ f = ArgMax Set.univ g := by
-- proof
  rw [h]


-- created on 2026-09-27

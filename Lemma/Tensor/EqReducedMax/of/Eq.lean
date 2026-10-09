import sympy.Basic
import sympy.concrete.expr_with_limits


@[path]
private lemma main
  [SupSet β]
  {f g : α → β}
-- given
  (h : f = g) :
-- imply
  Maxima Set.univ f = Maxima Set.univ g := by
-- proof
  rw [h]


-- created on 2021-09-07

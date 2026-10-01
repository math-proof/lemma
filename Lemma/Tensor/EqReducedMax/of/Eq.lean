import sympy.Basic
import sympy.concrete.expr_with_limits


@[main]
private lemma main
  [SupSet β]
  {f g : α → β}
-- given
  (h : f = g) :
-- imply
  Maxima Set.univ f = Maxima Set.univ g := by
-- proof
  rw [h]


-- created on 2026-09-27

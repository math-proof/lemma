import sympy.Basic
import Mathlib.Order.Filter.Defs


@[main]
private lemma main
  {l : Filter α}
  {p : Filter.Germ l β → Prop}
-- given
  (x : Filter.Germ l β)
  (h : ∀ x : α → β, p x) :
-- imply
  p x := by
-- proof
  refine Filter.Germ.inductionOn x h


-- created on 2025-12-09

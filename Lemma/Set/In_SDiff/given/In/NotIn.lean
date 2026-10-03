import sympy.Basic
import Lemma.Set.In_SDiff.is.In.NotIn


@[main]
private lemma main
  {x : α}
  {A B : Set α}
-- given
  (h : x ∈ A \ B) :
-- imply
  x ∈ A ∧ x ∉ B := by
-- proof
  exact Set.In.NotIn.of.In_SDiff h


-- created on 2026-10-03

import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {e : α}
  {A B : Set α}
-- given
  (h : e ∈ A \ B) :
-- imply
  e ∈ A ∧ e ∉ B :=
-- proof
  h


-- created on 2018-01-13

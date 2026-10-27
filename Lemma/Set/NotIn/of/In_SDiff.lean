import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {e : α}
  {S s : Set α}
-- given
  (h : e ∈ S \ s) :
-- imply
  e ∉ s :=
-- proof
  h.right


-- created on 2023-05-21

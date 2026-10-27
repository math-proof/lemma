import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [LinearOrder α]
  {x a : α}
-- given
  (h : x ≤ a) :
-- imply
  x ∉ Ioi a := by
-- proof
  contrapose! h
  assumption


-- created on 2019-02-07

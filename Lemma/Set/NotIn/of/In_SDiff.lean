import Lemma.Basic


@[main]
private lemma fin
  [DecidableEq α]
  {s S : Finset α}
  {e : α}
-- given
  (h : e ∈ S \ s) :
-- imply
  e ∉ s := by
-- proof
  simp_all


@[main]
private lemma main
  {s S : Set α}
  {e : α}
-- given
  (h : e ∈ S \ s) :
-- imply
  e ∉ s := by
-- proof
  exact h.right


-- created on 2025-04-05

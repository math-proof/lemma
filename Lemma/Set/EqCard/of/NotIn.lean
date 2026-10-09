import sympy.Basic


@[path]
private lemma main
  [DecidableEq α]
  {S : Finset α}
  {e : α}
-- given
  (h : e ∉ S) :
-- imply
  (S ∪ {e}).card = S.card + 1 := by
-- proof
  rw [Finset.union_singleton, Finset.card_insert_of_notMem h]


-- created on 2021-03-17

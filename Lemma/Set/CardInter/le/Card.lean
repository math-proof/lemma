import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [DecidableEq α]
  (A B : Finset α) :
-- imply
  (A ∩ B).card ≤ A.card := by
-- proof
  exact Finset.card_le_card fun _ hx => (Finset.mem_inter.mp hx).1


-- created on 2021-04-24

import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {S : Finset ℤ}
-- given
  (h : S.card ≥ 1) :
-- imply
  ∃ x, x ∈ S := by
-- proof
  exact Finset.card_pos.mp h


-- created on 2020-07-13

import Lemma.Bool.Bool.eq.Ite
open Bool


@[main]
private lemma main
  [DecidableEq α]
-- given
  (S : Finset α) :
-- imply
  ∑ i ∈ S, Bool.toNat (i ∈ S) = S.card := by
-- proof
  simp [Bool.eq.Ite]


-- created on 2020-07-03
-- updated on 2026-09-07

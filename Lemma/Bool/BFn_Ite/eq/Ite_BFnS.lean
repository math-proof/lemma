import Lemma.Bool.BFn_Ite.is.OrAndS
open Bool


@[main]
private lemma main
  [Decidable p]
-- given
  (f : α → β → γ)
  (c : α)
  (a b : β) :
-- imply
  f c (if p then
    a
  else
    b) = if p then
    f c a
  else
    f c b := by
-- proof
  apply BFn_Ite.of.OrAndS (R := Eq)
  -- This decomposes the proof into two cases: when `p` is true and when `p` is false.
  split_ifs <;>
    simp_all


-- created on 2025-04-12

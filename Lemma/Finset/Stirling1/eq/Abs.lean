import Lemma.Finset.StirlingSecond.eq.NcardParts
open Finset Stirling.conditionset


@[path]
private lemma main
-- given
  (n k : ℕ) :
-- imply
  Nat.stirlingSecond n k = (parts n k).ncard := by
-- proof
  apply StirlingSecond.eq.NcardParts


-- created on 2021-09-06
-- updated on 2026-10-17

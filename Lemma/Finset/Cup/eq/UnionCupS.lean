import Lemma.Finset.EqUnionInter__SDiff
import Lemma.Set.Eq.of.All_In.All_In
import Lemma.Set.In.of.In.Subset
import Lemma.Set.In_Union.is.OrInS
import Lemma.Finset.SubsetCupS.of.Subset
import Lemma.Finset.SubsetSDiff
import Lemma.Finset.In_CupIn_Union.is.OrInS_Cup
open Set Finset


@[main]
private lemma fn
  [DecidableEq α]
-- given
  (f : α → Finset β)
  (A B : Finset α) :
-- imply
  ⋃ k ∈ A, f k = (⋃ k ∈ A ∩ B, f k) ∪ ⋃ k ∈ (A \ B), (f k : Set β) := by
-- proof
  apply Eq.of.All_In.All_In
  ·
    intro k h_cup
    apply In_Union.of.OrInS
    apply OrInS_Cup.of.In_CupIn_Union
    rwa [EqUnionInter__SDiff A B]
  ·
    intro k h_union
    obtain h_inter | h_sdiff := OrInS.of.In_Union h_union <;>
      apply In.of.In.Subset _ (by assumption) <;>
      apply SubsetCupS.of.Subset
    ·
      simp
    ·
      apply SubsetSDiff


@[main]
private lemma main
  [DecidableEq α]
-- given
  (f : α → Set β)
  (A B : Finset α) :
-- imply
  ⋃ k ∈ A, f k = (⋃ k ∈ A ∩ B, f k) ∪ ⋃ k ∈ (A \ B), f k := by
-- proof
  apply Eq.of.All_In.All_In
  ·
    intro k h_cup
    apply In_Union.of.OrInS
    apply OrInS_Cup.of.In_CupIn_Union
    rwa [EqUnionInter__SDiff A B]
  ·
    intro k h_union
    obtain h_inter | h_sdiff := OrInS.of.In_Union h_union <;>
      apply In.of.In.Subset _ (by assumption) <;>
      apply SubsetCupS.of.Subset
    ·
      simp
    ·
      apply SubsetSDiff


-- created on 2025-12-30

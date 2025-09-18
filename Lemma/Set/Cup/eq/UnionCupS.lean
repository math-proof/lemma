import Lemma.Set.Eq.of.All_In.All_In
import Lemma.Set.In_Union.is.OrInS
import Lemma.Set.In_CupIn_Union.is.OrInS_Cup
import Lemma.Set.EqUnionInter__SDiff
import Lemma.Set.In.of.In.Subset
import Lemma.Set.SubsetCupS.of.Subset
import Lemma.Set.SubsetSDiff
open Set


@[main]
private lemma main
-- given
  (f : α → Set β)
  (A B : Set α) :
-- imply
  ⋃ x ∈ A, f x = (⋃ x ∈ A ∩ B, f x) ∪ ⋃ x ∈ A \ B, f x := by
-- proof
  apply Eq.of.All_In.All_In
  ·
    intro x h_cup
    apply In_Union.of.OrInS
    apply OrInS_Cup.of.In_CupIn_Union
    rwa [EqUnionInter__SDiff A B]
  ·
    intro x h_union
    obtain h_inter | h_sdiff := OrInS.of.In_Union h_union <;>
      apply In.of.In.Subset _ (by assumption) <;>
      apply SubsetCupS.of.Subset
    ·
      simp
    ·
      apply SubsetSDiff


@[main]
private lemma fin.fn
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
    apply OrInS_Cup.of.In_CupIn_Union.fin
    rwa [EqUnionInter__SDiff.fin A B]
  ·
    intro k h_union
    obtain h_inter | h_sdiff := OrInS.of.In_Union h_union <;>
      apply In.of.In.Subset _ (by assumption) <;>
      apply SubsetCupS.of.Subset.fin
    ·
      simp
    ·
      apply SubsetSDiff.fin


@[main]
private lemma fin
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
    apply OrInS_Cup.of.In_CupIn_Union.fin
    rwa [EqUnionInter__SDiff.fin A B]
  ·
    intro k h_union
    obtain h_inter | h_sdiff := OrInS.of.In_Union h_union <;>
      apply In.of.In.Subset _ (by assumption) <;>
      apply SubsetCupS.of.Subset.fin
    ·
      simp
    ·
      apply SubsetSDiff.fin


-- created on 2025-07-20
-- updated on 2025-08-14

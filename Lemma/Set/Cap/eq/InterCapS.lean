import Lemma.Set.EqUnionInter__SDiff
import Lemma.Set.Eq.of.All_In.All_In
import Lemma.Set.In_Inter.is.In.In
import Lemma.Set.In.of.In.Subset
import Lemma.Set.SubsetCapS.of.Supset
import Lemma.Set.Supset_SDiff
import Lemma.Set.In_CapIn_Union.of.In_Cap.In_Cap
open Set


@[main]
private lemma main
-- given
  (f : α → Set α)
  (A B : Set α) :
-- imply
  ⋂ x ∈ A, f x = (⋂ x ∈ A ∩ B, f x) ∩ ⋂ x ∈ A \ B, f x := by
-- proof
  apply Eq.of.All_In.All_In
  ·
    intro x h_cap
    apply In_Inter.of.In.In <;>
      apply In.of.In.Subset _ h_cap <;>
      apply SubsetCapS.of.Supset
    ·
      simp
    ·
      apply Supset_SDiff
  ·
    intro x h_inter
    let ⟨h_Inter, h_SDiff⟩ := In.In.of.In_Inter h_inter
    have h_Union := In_CapIn_Union.of.In_Cap.In_Cap h_Inter h_SDiff
    rwa [EqUnionInter__SDiff A B] at h_Union


-- created on 2025-07-20

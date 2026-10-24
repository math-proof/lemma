import Mathlib
import sympy.Basic
open Set Topology


namespace CompactnessArgument

/--
[compactness_argument](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/CompactnessArgument.lean)
-/
@[path]
lemma compactness_argument
  {α : V → Type*}
  [∀ v, Fintype (α v)]
  [∀ v, TopologicalSpace (α v)]
  [∀ v, DiscreteTopology (α v)]
  {events : Set (Set ((v : V) → α v))}
-- given
  (hclosed : ∀ A ∈ events, IsClosed Aᶜ)
  (hfin : ∀ F ⊆ events, F.Finite → ∃ f : (v : V) → α v, ∀ A ∈ F, f ∉ A) :
-- imply
  ∃ f : (v : V) → α v, ∀ A ∈ events, f ∉ A := by
-- proof
  set goods := compl '' events with hgoods_def
  have hgclosed : ∀ G ∈ goods, IsClosed G := by
    rintro G ⟨A, hA, rfl⟩
    exact hclosed A hA
  have hgfip : ∀ F ⊆ goods, F.Finite → (⋂₀ F).Nonempty := by
    intro F hFsub hFfin
    let eventsF := compl '' F
    have heFsub : eventsF ⊆ events := by
      rintro A ⟨G, hG, rfl⟩
      obtain ⟨B, hB, rfl⟩ := hFsub hG
      simpa using hB
    have heFfin : eventsF.Finite := hFfin.image _
    obtain ⟨f, hf⟩ := hfin eventsF heFsub heFfin
    refine ⟨f, mem_sInter.mpr (fun G hG => ?_)⟩
    obtain ⟨A, hA, rfl⟩ := hFsub hG
    simp only [mem_compl_iff]
    exact hf A (by exact ⟨Aᶜ, hG, compl_compl A⟩)
  have hne : (⋂₀ goods).Nonempty := CompactSpace.nonempty_sInter hgclosed hgfip
  obtain ⟨f, hf⟩ := hne
  exact ⟨f, fun A hA => by
    have : f ∈ Aᶜ := mem_sInter.mp hf (Aᶜ) ⟨A, hA, rfl⟩
    exact this⟩

end CompactnessArgument


-- created on 2026-10-23

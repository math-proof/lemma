import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.Building.Link
import Lemma.Finset.Disjoint.of.In_FacesLinkComplex.In_Faces
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
open SimplicialComplex in
open scoped Classical


/--
[linkComplex_maximal_union_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GalleryProjectionHelper.lean)
-/
@[path]
lemma linkComplex_maximal_union_maximal
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {σ : Finset V}
  {C : Finset V}
-- given
  (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
  (hC : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C) :
-- imply
  b.toChamberComplex.toSimplicialComplex.IsMaximal (σ ∪ C) := by
-- proof
  set K := b.toChamberComplex.toSimplicialComplex
  have hC_link := hC.1
  rw [mem_linkComplex_iff] at hC_link
  refine ⟨hC_link.2.2, fun w hw h_sub => ?_⟩
  have hσw : σ ⊆ w := Finset.subset_union_left.trans h_sub
  by_cases hne : (w \ σ).Nonempty
  · have hw_link := mem_linkComplex_of_sdiff K σ hσ w hw hσw hne
    have hC_sub : C ⊆ w \ σ := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨h_sub (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hC_link.2.1 hv⟩
    rw [hC.2 (w \ σ) hw_link hC_sub, Finset.union_sdiff_of_subset hσw]
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
    exfalso
    obtain ⟨v, hv⟩ := hC_link.1
    exact Finset.disjoint_right.mp hC_link.2.1 hv (hne (h_sub (Finset.mem_union_right σ hv)))

private lemma union_ne_of_disjoint_ne
  {V : Type}
  [DecidableEq V]
  {σ C D : Finset V}
-- given
  (hC_disj : Disjoint σ C)
  (hD_disj : Disjoint σ D)
  (hne : C ≠ D) :
-- imply
  σ ∪ C ≠ σ ∪ D := by
-- proof
  intro h
  apply hne
  have hC' : C = (σ ∪ C) \ σ := (Finset.union_sdiff_cancel_left hC_disj).symm
  have hD' : D = (σ ∪ D) \ σ := (Finset.union_sdiff_cancel_left hD_disj).symm
  rw [hC', hD', h]
-- Axiom-form of the link distance bound: the gallery distance in the link
-- $\mathrm{lk}_\sigma$ between maximal faces $C, D$ is bounded by the gallery
-- distance between the chambers $\sigma \cup C, \sigma \cup D$ in the ambient
-- building.


-- created on 2026-10-24

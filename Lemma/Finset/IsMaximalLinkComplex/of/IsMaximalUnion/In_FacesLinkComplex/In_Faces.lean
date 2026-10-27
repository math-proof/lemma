import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.Building.Link
import Lemma.Finset.Disjoint.of.In_FacesLinkComplex.In_Faces
import Lemma.Int.Pow.eq.OneOrEqPow.of.EqMul_1
import Def.v1.Atlas.Buildings.code.CoxeterGroup.ParabolicSubgroups


/--
[linkComplex_maximal_of_union_maximal_local](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LinkCoxeterHelper.lean)
-/
@[path]
lemma linkComplex_maximal_of_union_maximal_local
  [DecidableEq V]
  {K : SimplicialComplex V}
  {σ : Finset V}
  {τ : Finset V}
-- given
  (hσ : σ ∈ K.faces)
  (hτ_link : τ ∈ (K.linkComplex σ hσ).faces)
  (hστ_max : K.IsMaximal (σ ∪ τ)) :
-- imply
  (K.linkComplex σ hσ).IsMaximal τ := by
-- proof
  have hτ_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ τ).mp hτ_link
  refine ⟨hτ_link, fun y hy hτy => ?_⟩
  have hy_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ y).mp hy
  have h_eq := hστ_max.2 (σ ∪ y) hy_data.2.2 (Finset.union_subset_union_right hτy)
  ext v
  constructor
  · intro hv
    have := h_eq ▸ (Finset.mem_union_right σ hv)
    exact (Finset.mem_union.mp this).elim
      (fun h => absurd h (Finset.disjoint_right.mp hτ_data.2.1 hv)) id
  · intro hv
    have := h_eq.symm ▸ (Finset.mem_union_right σ hv)
    exact (Finset.mem_union.mp this).elim
      (fun h => absurd h (Finset.disjoint_right.mp hy_data.2.1 hv)) id

private lemma link_cc_exists_maximal
  [DecidableEq V]
  {A : SimplicialComplex V}
  {cc : ChamberComplex V}
  {σ : Finset V}
-- given
  (hcc_eq : cc.toSimplicialComplex = A)
  (hσ : σ ∈ A.faces)
  (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
-- imply
  ∀ s ∈ (A.linkComplex σ hσ).faces, ∃ C, (A.linkComplex σ hσ).IsMaximal C ∧ s ⊆ C := by
-- proof
  intro s hs
  have hs_data := (SimplicialComplex.mem_linkComplex_iff A σ hσ s).mp hs
  have hσs_in_A : σ ∪ s ∈ A.faces := hs_data.2.2
  have hσs_in_cc : σ ∪ s ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hσs_in_A
  obtain ⟨C, hC_max_cc, hσs_sub⟩ := cc.exists_maximal (σ ∪ s) hσs_in_cc
  have hC_max : A.IsMaximal C := hcc_eq ▸ hC_max_cc
  have hσ_sub_C : σ ⊆ C := Finset.subset_union_left.trans hσs_sub
  have hne : (C \ σ).Nonempty := by
    obtain ⟨v, hv⟩ := hs_data.1
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hσs_sub (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hs_data.2.1 hv⟩⟩
  have hCσ_link := SimplicialComplex.mem_linkComplex_of_sdiff A σ hσ C hC_max.1 hσ_sub_C hne
  have hC_eq : σ ∪ (C \ σ) = C := Finset.union_sdiff_of_subset hσ_sub_C
  have hCσ_max_A : A.IsMaximal (σ ∪ (C \ σ)) := by rw [hC_eq]; exact hC_max
  have hCσ_max_lk : (A.linkComplex σ hσ).IsMaximal (C \ σ) :=
    linkComplex_maximal_of_union_maximal_local hσ hCσ_link hCσ_max_A
  have hs_sub : s ⊆ C \ σ := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hσs_sub (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hs_data.2.1 hv⟩
  exact ⟨C \ σ, hCσ_max_lk, hs_sub⟩
-- The link of a face in a Coxeter complex carries a thin chamber complex structure, packaging
-- the existence of maximals, gallery-connectedness, and thinness.


-- created on 2026-10-24

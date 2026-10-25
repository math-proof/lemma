import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.Building.ThicknessFoldings
open ChamberComplex AptIsCoxeterProof ThicknessFoldings


/--
[chain_transition](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma chain_transition_eq
  {V : Type}
  [DecidableEq V]
  {l : List α}
-- given
  (R : α → α → Prop)
  (P : α → Prop)
  (hchain : List.IsChain R l)
  (hl : l ≠ [])
  (hhead : P (l.head hl))
  (hE : ∃ e ∈ l, ¬P e) :
-- imply
  ∃ a b, a ∈ l ∧ b ∈ l ∧ R a b ∧ P a ∧ ¬P b := by
-- proof
  apply chain_transition R P l hchain hl hhead hE

/--
[apt_is_thin_pre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma apt_is_thin_pre_eq
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
-- given
  (hA : A ∈ pre.apartments) :
-- imply
  ∀ F C, A.IsFacet F C → A.IsMaximal C → ∃! D, D ≠ C ∧ A.IsFacet F D ∧ A.IsMaximal D := by
-- proof
  apply ThicknessFoldings.apt_is_thin_pre K pre A hA

/--
[apt_automorphism_sending_chamber_pre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma apt_automorphism_sending_chamber_pre_eq
  {V : Type}
  [DecidableEq V]
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
  {C : Finset V}
  {D : Finset V}
-- given
  (hA : A ∈ pre.apartments)
  (hC : A.IsMaximal C)
  (hD : A.IsMaximal D) :
-- imply
  ∃ (φ : V → V), Function.Bijective φ ∧ (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧ D.image φ = C := by
-- proof
  apply ThicknessFoldings.apt_automorphism_sending_chamber_pre pre A hA C hC D hD

/--
[bij_iso_fixing_chamber_is_id_pre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma bij_iso_fixing_chamber_is_id_pre_eq
  {V : Type}
  [DecidableEq V]
  {pre : PreApartmentData K}
  {B B' : SimplicialComplex V}
  {D : Finset V}
  {φ : V → V}
-- given
  (hB : B ∈ pre.apartments)
  (hD_B : D ∈ B.faces)
  (hD_max : K.toSimplicialComplex.IsMaximal D)
  (hφ_bij : Function.Bijective φ)
  (_hφ_faces : ∀ s, s ∈ B.faces ↔ s.image φ ∈ B'.faces)
  (hφ_D : D.image φ = D) :
-- imply
  ∀ s ∈ B.faces, s.image φ = s := by
-- proof
  apply ThicknessFoldings.bij_iso_fixing_chamber_is_id_pre pre B B' hB D hD_B hD_max φ hφ_bij _hφ_faces hφ_D

/--
[iso_bijective_fixing_chamber_pre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma iso_bijective_fixing_chamber_pre_eq
  {V : Type}
  [DecidableEq V]
  {pre : PreApartmentData K}
  {B : SimplicialComplex V}
  {B₀ : SimplicialComplex V}
  {D : Finset V}
-- given
  (hB : B ∈ pre.apartments)
  (hB₀ : B₀ ∈ pre.apartments)
  (hD_B : D ∈ B.faces)
  (hD_B₀ : D ∈ B₀.faces)
  (hD_max_B : B.IsMaximal D) :
-- imply
  ∃ (φ : V → V), Function.Bijective φ ∧ (∀ s, s ∈ B.faces ↔ s.image φ ∈ B₀.faces) ∧ D.image φ = D := by
-- proof
  apply ThicknessFoldings.iso_bijective_fixing_chamber_pre pre B hB B₀ hB₀ D hD_B hD_B₀ hD_max_B

/--
[exists_canonical_retraction_pre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma exists_canonical_retraction_pre_eq
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ pre.apartments)
  (hC : A.IsMaximal C) :
-- imply
  ∃ (ρ : V → V), (∀ s ∈ K.toSimplicialComplex.faces, s.image ρ ∈ A.faces) ∧ (∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ v = v) ∧ (∀ D, K.toSimplicialComplex.IsMaximal D → A.IsMaximal (D.image ρ)) ∧ (∀ D₁ D₂, K.toSimplicialComplex.Adjacent D₁ D₂ → D₁.image ρ = D₂.image ρ ∨ A.Adjacent (D₁.image ρ) (D₂.image ρ)) ∧ (∀ (B : SimplicialComplex V), B ∈ pre.apartments → C ∈ B.faces → ∀ v₁ v₂, (∃ s ∈ B.faces, v₁ ∈ s) → (∃ s ∈ B.faces, v₂ ∈ s) → ρ v₁ = ρ v₂ → v₁ = v₂) ∧ (∀ v, ∃ s ∈ A.faces, ρ v ∈ s) ∧ (∀ (B : SimplicialComplex V), B ∈ pre.apartments → C ∈ B.faces → ∀ (σ : V → V), (∀ s ∈ K.toSimplicialComplex.faces, s.image σ ∈ B.faces) → (∀ v, (∃ s ∈ B.faces, v ∈ s) → σ v = v) → ∀ v, (∃ s ∈ A.faces, v ∈ s) → ρ (σ v) = v) := by
-- proof
  apply ThicknessFoldings.exists_canonical_retraction_pre K pre A hA C hC

/--
[apt_facet_of_maximal_containing_pre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma apt_facet_of_maximal_containing_pre_eq
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
  {C D F₀ : Finset V}
-- given
  (hA : A ∈ pre.apartments)
  (hC_max : A.IsMaximal C)
  (hD_max : A.IsMaximal D)
  (hF₀_C : A.IsFacet F₀ C)
  (hF₀_sub_D : F₀ ⊆ D) :
-- imply
  A.IsFacet F₀ D := by
-- proof
  apply ThicknessFoldings.apt_facet_of_maximal_containing_pre K pre A hA hC_max hD_max hF₀_C hF₀_sub_D

/--
[thin_unique_other_chamber_pre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma thin_unique_other_chamber_pre_eq
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
  {F C D₁ D₂ : Finset V}
-- given
  (hA : A ∈ pre.apartments)
  (hC_max : A.IsMaximal C)
  (hF_C : A.IsFacet F C)
  (hD₁_max : A.IsMaximal D₁)
  (hD₁_ne : D₁ ≠ C)
  (hF_D₁ : A.IsFacet F D₁)
  (hD₂_max : A.IsMaximal D₂)
  (hD₂_ne : D₂ ≠ C)
  (hF_D₂ : A.IsFacet F D₂) :
-- imply
  D₁ = D₂ := by
-- proof
  apply ThicknessFoldings.thin_unique_other_chamber_pre K pre hA hC_max hF_C hD₁_max hD₁_ne hF_D₁ hD₂_max hD₂_ne hF_D₂

/--
[apt_chamber_with_facet_is_C_or_C_pre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma apt_chamber_with_facet_is_C_or_C_pre_eq
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
  {C C' D F₀ : Finset V}
-- given
  (hA : A ∈ pre.apartments)
  (hC_max : A.IsMaximal C)
  (hC'_max : A.IsMaximal C')
  (hD_max : A.IsMaximal D)
  (hne : C ≠ C')
  (hF₀_C : A.IsFacet F₀ C)
  (hF₀_C' : A.IsFacet F₀ C')
  (hF₀_sub_D : F₀ ⊆ D) :
-- imply
  D = C ∨ D = C' := by
-- proof
  apply ThicknessFoldings.apt_chamber_with_facet_is_C_or_C_pre K pre hA hC_max hC'_max hD_max hne hF₀_C hF₀_C' hF₀_sub_D

/--
[exists_map_fixing_sending_adj_pre](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma exists_map_fixing_sending_adj_pre_eq
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
  {C C' : Finset V}
-- given
  (hK_thick : K.IsThick)
  (hA : A ∈ pre.apartments)
  (hC_A : A.IsMaximal C)
  (hC'_A : A.IsMaximal C')
  (hadj_A : A.Adjacent C C') :
-- imply
  ∃ f : V → V, C.image f = C ∧ C'.image f = C ∧ (∀ s ∈ A.faces, s.image f ∈ A.faces) ∧ (∀ v, f (f v) = f v) ∧ (∀ D, A.IsMaximal D → A.IsMaximal (D.image f)) ∧ (∀ F D, A.IsFacet F D → A.IsFacet (F.image f) (D.image f)) ∧ (∀ (cc : ChamberComplex V), cc.toSimplicialComplex = A → ∀ D, cc.toSimplicialComplex.IsMaximal D → D.image f = D → ∃! D', cc.toSimplicialComplex.IsMaximal D' ∧ D' ≠ D ∧ D'.image f = D) ∧ (∀ (cc : ChamberComplex V), cc.toSimplicialComplex = A → ∀ (A₀ B : Finset V), cc.toSimplicialComplex.IsMaximal A₀ → A₀.image f = A₀ → cc.toSimplicialComplex.IsMaximal B → B.image f = B → ∀ (g : Gallery cc.toSimplicialComplex), g.Connects A₀ B → g.length = galleryDist cc.toSimplicialComplex A₀ B → ∀ (Ci Ci1 : Finset V), Ci ∈ g.chambers → Ci1 ∈ g.chambers → cc.toSimplicialComplex.Adjacent Ci Ci1 → Ci1.image f = Ci.image f → False) := by
-- proof
  apply ThicknessFoldings.exists_map_fixing_sending_adj_pre K hK_thick pre A hA C C' hC_A hC'_A hadj_A

/--
[folding_from_simplicial_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma folding_from_simplicial_map_eq
  {V : Type}
  [DecidableEq V]
  {cc : ChamberComplex V}
  {f : V → V}
  {C C' : Finset V}
-- given
  (hthin : cc.IsThin)
  (hface : ∀ s ∈ cc.toSimplicialComplex.faces, s.image f ∈ cc.toSimplicialComplex.faces)
  (hidempotent : ∀ v, f (f v) = f v)
  (hchamberMap : ∀ D, cc.toSimplicialComplex.IsMaximal D → cc.toSimplicialComplex.IsMaximal (D.image f))
  (hpreservesFacets : ∀ F D, cc.toSimplicialComplex.IsFacet F D → cc.toSimplicialComplex.IsFacet (F.image f) (D.image f))
  (htwoToOne : ∀ D, cc.toSimplicialComplex.IsMaximal D → D.image f = D → ∃! D', cc.toSimplicialComplex.IsMaximal D' ∧ D' ≠ D ∧ D'.image f = D)
  (hstutter_contradicts_minimality : ∀ (A B : Finset V), cc.toSimplicialComplex.IsMaximal A → A.image f = A → cc.toSimplicialComplex.IsMaximal B → B.image f = B → ∀ (g : Gallery cc.toSimplicialComplex), g.Connects A B → g.length = galleryDist cc.toSimplicialComplex A B → ∀ (Ci Ci1 : Finset V), Ci ∈ g.chambers → Ci1 ∈ g.chambers → cc.toSimplicialComplex.Adjacent Ci Ci1 → Ci1.image f = Ci.image f → False)
  (hadj : cc.toSimplicialComplex.Adjacent C C')
  (hfC : C.image f = C)
  (hfC' : C'.image f = C) :
-- imply
  ∃ fold : Folding cc, C.image fold.morph.toFun = C ∧ C'.image fold.morph.toFun = C := by
-- proof
  apply ThicknessFoldings.folding_from_simplicial_map cc hthin f hface hidempotent hchamberMap hpreservesFacets htwoToOne hstutter_contradicts_minimality C C' hadj hfC hfC'

/--
[apt_has_sufficient_foldings](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma apt_has_sufficient_foldings_eq
  {V : Type}
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
  {cc : ChamberComplex V}
-- given
  (hK_thick : K.IsThick)
  (hA : A ∈ pre.apartments)
  (hcc_eq : cc.toSimplicialComplex = A)
  (hcc_thin : cc.IsThin) :
-- imply
  HasSufficientFoldings cc := by
-- proof
  apply ThicknessFoldings.apt_has_sufficient_foldings K hK_thick pre A hA cc hcc_eq hcc_thin

/--
[thickness_implies_apt_structure_hyp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessFoldings.lean)
-/
@[path]
private lemma thickness_implies_apt_structure_hyp_eq
  {V : Type}
  [DecidableEq V] :
-- imply
  ThicknessImpliesAptStructureHyp V := by
-- proof
  apply ThicknessFoldings.thickness_implies_apt_structure_hyp


-- created on 2026-10-23

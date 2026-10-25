import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.ChamberComplex.GalleryTypes.CoxeterProperties.Part2
open ChamberComplex
open scoped Classical


/--
[hasSufficientReversibleFoldings_separatedByWall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/GalleryTypes/CoxeterProperties.lean)
-/
@[path]
lemma hasSufficientReversibleFoldings_separatedByWall
  [DecidableEq V]
  {K : ChamberComplex V}
  {C D : Finset V}
-- given
  (hSRF : HasSufficientReversibleFoldings K)
  (hadj : K.toSimplicialComplex.Adjacent C D) :
-- imply
  SeparatedByWall K C D := by
-- proof
  obtain ⟨rf, hfC, hfD_eq_C, _, _⟩ := hSRF C D hadj
  have hne : C ≠ D := hadj.2.2.1
  have hfD_ne : D.image rf.f.morph.toFun ≠ D := by
    intro h; rw [hfD_eq_C] at h; exact hne h
  exact ⟨rf, Or.inl ⟨hfC, hfD_ne⟩⟩


private lemma separatedByWall_hasSufficientReversibleFoldings
  [DecidableEq V]
  {K : ChamberComplex V}
-- given
  (hThin : K.IsThin)
  (hSep : ∀ C D, K.toSimplicialComplex.Adjacent C D → SeparatedByWall K C D) :
-- imply
  HasSufficientReversibleFoldings K := by
-- proof
  intro C D hadj
  obtain ⟨rf, hopp⟩ := hSep C D hadj
  obtain ⟨hfC, hfD_ne⟩ | ⟨hfD, hfC_ne⟩ := hopp
  ·
    have hfD_eq_C : D.image rf.f.morph.toFun = C :=
      Folding.fold_adj_to_self rf.f hThin hadj hfC hfD_ne
    have hgC_ne : C.image rf.g.morph.toFun ≠ C := by
      intro h
      have hC_in_g_fixed : C ∈ rf.g.fixedChambers := ⟨hadj.1, h⟩
      have hC_in_f_fixed : C ∈ rf.f.fixedChambers := ⟨hadj.1, hfC⟩
      exact rf.halves_disjoint C ⟨hC_in_f_fixed, hC_in_g_fixed⟩
    have hgD : D.image rf.g.morph.toFun = D := by
      have hD_in_f_moved : D ∈ rf.f.movedChambers := ⟨hadj.2.1, hfD_ne⟩
      have hD_in_g_fixed : D ∈ rf.g.fixedChambers :=
        rf.complementary_moved ▸ hD_in_f_moved
      exact hD_in_g_fixed.2
    have hadj' : K.toSimplicialComplex.Adjacent D C := by
      obtain ⟨hCmax, hDmax, hne, F, hFC, hFD⟩ := hadj
      exact ⟨hDmax, hCmax, hne.symm, F, hFD, hFC⟩
    have hgC_eq_D : C.image rf.g.morph.toFun = D :=
      Folding.fold_adj_to_self rf.g hThin hadj' hgD hgC_ne
    exact ⟨rf, hfC, hfD_eq_C, hgD, hgC_eq_D⟩
  ·
    have hadj' : K.toSimplicialComplex.Adjacent D C := by
      obtain ⟨hCmax, hDmax, hne, F, hFC, hFD⟩ := hadj
      exact ⟨hDmax, hCmax, hne.symm, F, hFD, hFC⟩
    have hfC_eq_D : C.image rf.f.morph.toFun = D :=
      Folding.fold_adj_to_self rf.f hThin hadj' hfD hfC_ne
    have hgD_ne : D.image rf.g.morph.toFun ≠ D := by
      intro h
      have hD_in_g_fixed : D ∈ rf.g.fixedChambers := ⟨hadj.2.1, h⟩
      have hD_in_f_fixed : D ∈ rf.f.fixedChambers := ⟨hadj.2.1, hfD⟩
      exact rf.halves_disjoint D ⟨hD_in_f_fixed, hD_in_g_fixed⟩
    have hgC : C.image rf.g.morph.toFun = C := by
      have hC_in_f_moved : C ∈ rf.f.movedChambers := ⟨hadj.1, hfC_ne⟩
      have hC_in_g_fixed : C ∈ rf.g.fixedChambers :=
        rf.complementary_moved ▸ hC_in_f_moved
      exact hC_in_g_fixed.2
    have hgD_eq_C : D.image rf.g.morph.toFun = C :=
      Folding.fold_adj_to_self rf.g hThin hadj hgC hgD_ne
    let rf' : ReversibleFolding K := {
      f := rf.g
      g := rf.f
      complementary_fixed := rf.complementary_moved.symm
      complementary_moved := rf.complementary_fixed.symm
      opposite_action := rf.opposite_action'
      opposite_action' := rf.opposite_action
    }
    exact ⟨rf', hgC, hgD_eq_C, hfD, hfC_eq_D⟩


private lemma hasSufficientReversibleFoldings_hasSufficientFoldings
  [DecidableEq V]
  {K : ChamberComplex V}
-- given
  (hSRF : HasSufficientReversibleFoldings K) :
-- imply
  AptIsCoxeterProof.HasSufficientFoldings K := by
-- proof
  intro C C' hadj
  obtain ⟨rf, hfC, hfC'_eq_C, hgC', hgC_eq_C'⟩ := hSRF C C' hadj
  exact ⟨rf.f, rf.g, hfC, hfC'_eq_C, hgC', hgC_eq_C'⟩


private lemma isCoxeterComplex_thinWithFoldings
  [DecidableEq V]
  [DecidableEq V]
  {K : ChamberComplex V} :
-- imply
  IsCoxeterComplex K → K.IsThin ∧ HasSufficientReversibleFoldings K := by
-- proof
  intro hCox
  obtain ⟨B_idx, M, φ, hinj, hsurj, hadj_fwd, hadj_bwd, hfacet_shared⟩ := hCox
  constructor
  ·
    intro F C hFC hC
    have uniqueness : ∀ D₁ D₂,
      (D₁ ≠ C ∧ K.toSimplicialComplex.IsFacet F D₁ ∧
        K.toSimplicialComplex.IsMaximal D₁) →
      (D₂ ≠ C ∧ K.toSimplicialComplex.IsFacet F D₂ ∧
        K.toSimplicialComplex.IsMaximal D₂) →
      D₁ = D₂ := by
      intro D₁ D₂ ⟨hD₁_ne, hFD₁, hD₁_max⟩ ⟨hD₂_ne, hFD₂, hD₂_max⟩
      by_contra hD₁D₂
      have hAdj_C_D₁ : K.toSimplicialComplex.Adjacent C D₁ :=
        ⟨hC, hD₁_max, hD₁_ne.symm, F, hFC, hFD₁⟩
      have hAdj_C_D₂ : K.toSimplicialComplex.Adjacent C D₂ :=
        ⟨hC, hD₂_max, hD₂_ne.symm, F, hFC, hFD₂⟩
      have hAdj_D₁_D₂ : K.toSimplicialComplex.Adjacent D₁ D₂ :=
        ⟨hD₁_max, hD₂_max, hD₁D₂, F, hFD₁, hFD₂⟩
      have h₁₂ := hadj_fwd C D₁ hAdj_C_D₁
      have h₁₃ := hadj_fwd C D₂ hAdj_C_D₂
      have h₂₃ := hadj_fwd D₁ D₂ hAdj_D₁_D₂
      exact AptIsCoxeterProof.coxeter_cayley_no_triangle M (φ C) (φ D₁) (φ D₂) h₁₂ h₂₃ h₁₃
    have existence : ∃ D, D ≠ C ∧ K.toSimplicialComplex.IsFacet F D ∧
      K.toSimplicialComplex.IsMaximal D := by
      obtain ⟨i, hi⟩ := coxeterComplex_facet_generator K B_idx M φ hinj hsurj
        hadj_fwd hadj_bwd hfacet_shared F C hFC hC
      obtain ⟨D, hD_max, hφD⟩ := hsurj (φ C * M.toCoxeterSystem.simple i)
      have hFD : K.toSimplicialComplex.IsFacet F D := hi D hD_max hφD
      have hD_ne : D ≠ C := by
        intro heq
        rw [heq] at hφD
        exact absurd (congrArg M.toCoxeterSystem.length hφD.symm)
          (M.toCoxeterSystem.length_mul_simple_ne (φ C) i)
      exact ⟨D, hD_ne, hFD, hD_max⟩
    obtain ⟨D, hD_ne, hFD, hD_max⟩ := existence
    exact ⟨D, ⟨hD_ne, hFD, hD_max⟩, fun D' ⟨hD'_ne, hFD', hD'_max⟩ =>
      (uniqueness D' D ⟨hD'_ne, hFD', hD'_max⟩ ⟨hD_ne, hFD, hD_max⟩)⟩
  ·
    exact fun C D hadj => coxeterReversibleFolding K B_idx M φ hinj hsurj hadj_fwd hadj_bwd C D hadj


private lemma coxeter_iff_adjacent_separated_by_wall
  [DecidableEq V]
  {K : ChamberComplex V} :
-- imply
  IsCoxeterComplex K ↔ (K.IsThin ∧ ∀ C D, K.toSimplicialComplex.Adjacent C D → SeparatedByWall K C D) := by
-- proof
  constructor
  ·
    intro hCox
    obtain ⟨hThin, hSRF⟩ := isCoxeterComplex_thinWithFoldings K hCox
    exact ⟨hThin, fun C D hadj =>
      hasSufficientReversibleFoldings_separatedByWall K hSRF C D hadj⟩
  ·
    intro ⟨hThin, hSep⟩
    have hSRF := separatedByWall_hasSufficientReversibleFoldings K hThin hSep
    have hSF : AptIsCoxeterProof.HasSufficientFoldings K :=
      hasSufficientReversibleFoldings_hasSufficientFoldings K hSRF
    exact thinWithFoldings_isCoxeterComplex K hThin hSF


private lemma injective_image_ne_of_ne
  [DecidableEq V]
  {K : ChamberComplex V}
  {f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex}
  {C D : Finset V}
-- given
  (hinj : Function.Injective f.toFun)
  (_hC : C ∈ K.toSimplicialComplex.faces)
  (_hD : D ∈ K.toSimplicialComplex.faces)
  (hne : C ≠ D) :
-- imply
  C.image f.toFun ≠ D.image f.toFun := by
-- proof
  intro heq
  apply hne
  ext v
  constructor
  · intro hv
    have : f.toFun v ∈ D.image f.toFun := by
      rw [← heq]; exact Finset.mem_image_of_mem _ hv
    rw [Finset.mem_image] at this
    obtain ⟨w, hw, hfw⟩ := this
    exact hinj hfw ▸ hw
  · intro hv
    have : f.toFun v ∈ C.image f.toFun := by
      rw [heq]; exact Finset.mem_image_of_mem _ hv
    rw [Finset.mem_image] at this
    obtain ⟨w, hw, hfw⟩ := this
    exact hinj hfw ▸ hw


private lemma injective_no_stutter
  [DecidableEq V]
  {K : ChamberComplex V}
  {f : SimplicialComplex.Morphism K.toSimplicialComplex K.toSimplicialComplex}
  {γ : Gallery K.toSimplicialComplex}
-- given
  (hinj : Function.Injective f.toFun) :
-- imply
  ¬ ImageGalleryStutters f γ.chambers := by
-- proof
  intro ⟨i, hi, heq⟩
  let fi : Fin γ.chambers.length := ⟨i, by omega⟩
  let fi1 : Fin γ.chambers.length := ⟨i + 1, hi⟩
  have hC_mem : γ.chambers.get fi ∈ γ.chambers := List.get_mem γ.chambers fi
  have hD_mem : γ.chambers.get fi1 ∈ γ.chambers := List.get_mem γ.chambers fi1
  have hC_max := γ.all_maximal _ hC_mem
  have hD_max := γ.all_maximal _ hD_mem
  have hchain := γ.adjacent_consecutive
  have hadj : K.toSimplicialComplex.Adjacent (γ.chambers.get fi) (γ.chambers.get fi1) := by
    rw [List.isChain_iff_getElem] at hchain
    have := hchain i hi
    simp only [List.get_eq_getElem] at this ⊢
    exact this
  have hne : γ.chambers.get fi ≠ γ.chambers.get fi1 := hadj.2.2.1
  exact injective_image_ne_of_ne f hinj hC_max.1 hD_max.1 hne heq


private lemma hasSufficientReversibleFoldings_folding_maps_adj_to_self_eq
  [DecidableEq V]
  {K : ChamberComplex V}
-- given
  (hSRF : HasSufficientReversibleFoldings K) :
-- imply
  ∀ C D, K.toSimplicialComplex.Adjacent C D → ∃ f : Folding K, C.image f.morph.toFun = C ∧ D.image f.morph.toFun = C := by
-- proof
  apply ChamberComplex.hasSufficientReversibleFoldings_folding_maps_adj_to_self K hSRF

private lemma thinWithFoldings_isCoxeterComplex_eq
  [DecidableEq V]
  [DecidableEq V]
  {K : ChamberComplex V} :
-- imply
  K.IsThin → AptIsCoxeterProof.HasSufficientFoldings K → IsCoxeterComplex K := by
-- proof
  apply ChamberComplex.thinWithFoldings_isCoxeterComplex K


-- created on 2026-10-24

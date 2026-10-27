import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.LieGroups.code.HarishChandraFunctor
open scoped Manifold


/--
[kFiniteSubspace_dense_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma kFiniteSubspace_dense_admissible
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K_sub : Subgroup G}
  [CompactSpace K_sub]
-- given
  (hadm : π.IsAdmissible K_sub) :
-- imply
  Dense (π.kFiniteSubspace K_sub : Set F) := by
-- proof
  obtain ⟨R, hR_kfin, hR_dirac, hR_pw⟩ :=
    ContinuousRep.measureRep_exists π K_sub
  intro v
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [mem_nhds_iff] at hU
  obtain ⟨t, htU, ht_open, hv_t⟩ := hU
  have ht_nhds_v : t ∈ nhds v := ht_open.mem_nhds hv_t
  obtain ⟨f, hft⟩ := hR_dirac v t ht_nhds_v
  have ht_nhds_Rfv : t ∈ nhds (R f v) := ht_open.mem_nhds hft
  obtain ⟨g, hg_kfin, hgt⟩ := hR_pw f v t ht_nhds_Rfv
  have hRg_kfin : R g v ∈ (π.kFiniteSubspace K_sub : Set F) := hR_kfin g v hg_kfin
  exact ⟨R g v, htU hgt, hRg_kfin⟩

/--
[iterLieAction_mem_kFiniteSubspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma iterLieAction_mem_kFiniteSubspace
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K_sub : Subgroup G}
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F)}
  {Xs : List 𝔤}
  {v : F}
-- given
  (hι_stable : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub → (ι X) w ∈ π.kFiniteSubspace K_sub)
  (hv : v ∈ π.kFiniteSubspace K_sub) :
-- imply
  iterLieAction ι Xs v ∈ π.kFiniteSubspace K_sub := by
-- proof
  induction Xs with
  | nil => exact hv
  | cons X rest ih =>
    simp only [iterLieAction, List.foldr_cons]
    exact hι_stable X _ ih

/--
[iterLieAction_agree_of_eq_on_kFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma iterLieAction_agree_of_eq_on_kFinite
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K_sub : Subgroup G}
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {ι₁ ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F)}
  {Xs : List 𝔤}
  {v : F}
-- given
  (hlie_eq : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub → (ι₁ X) w = (ι₂ X) w)
  (hι₁_stable : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub → (ι₁ X) w ∈ π.kFiniteSubspace K_sub)
  (hι₂_stable : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub → (ι₂ X) w ∈ π.kFiniteSubspace K_sub)
  (hv : v ∈ π.kFiniteSubspace K_sub) :
-- imply
  iterLieAction ι₁ Xs v = iterLieAction ι₂ Xs v := by
-- proof
  induction Xs with
  | nil => rfl
  | cons X rest ih =>
    show (ι₁ X) (iterLieAction ι₁ rest v) = (ι₂ X) (iterLieAction ι₂ rest v)
    rw [ih, hlie_eq X _ (iterLieAction_mem_kFiniteSubspace I π K_sub 𝔤 ι₂ hι₂_stable rest v hv)]

/--
[separation_from_closed_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma separation_from_closed_submodule
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {S : Submodule ℂ F}
  {x : F}
-- given
  (hS : IsClosed (S : Set F))
  (hx : x ∉ S) :
-- imply
  ∃ h : F →L[ℂ] ℂ, (∀ s ∈ S, h s = 0) ∧ h x ≠ 0 := by
-- proof
  haveI : IsClosed (S : Set F) := hS
  have hx_bar : (Submodule.Quotient.mk (p := S) x : F ⧸ S) ≠ 0 := by
    rwa [ne_eq, Submodule.Quotient.mk_eq_zero]
  obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) (V := F ⧸ S) hx_bar
  have hcont : Continuous S.mkQ := continuous_quotient_mk'
  set h := g.comp (⟨S.mkQ, hcont⟩ : F →L[ℂ] F ⧸ S) with hh_def
  refine ⟨h, ?_, ?_⟩
  · intro s hs
    simp only [hh_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk']
    have : (Submodule.Quotient.mk (p := S) s : F ⧸ S) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hs
    simp [this]
  · simp only [hh_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk']
    exact hg

/--
[iterLieAction_mem_image_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma iterLieAction_mem_image_submodule
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [AddCommGroup F]
  [Module ℂ F]
  {V : Submodule ℂ F}
  {ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F)}
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {W : Submodule ℂ V}
  {Xs : List 𝔤}
  {w : V}
-- given
  (hι_compat : ∀ (X : 𝔤) (w : V), V.subtype ⁅X, w⁆ = ι X (V.subtype w))
  (hW_lie : ∀ (X : 𝔤) (w : V), w ∈ W → ⁅X, w⁆ ∈ W)
  (hw : w ∈ W) :
-- imply
  iterLieAction ι Xs (V.subtype w) ∈ Submodule.map V.subtype W := by
-- proof
  induction Xs with
  | nil =>
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  | cons X Xs ih =>
    change ι X (iterLieAction ι Xs (V.subtype w)) ∈ Submodule.map V.subtype W
    obtain ⟨w', hw', heq⟩ := Submodule.mem_map.mp ih
    rw [← heq, ← hι_compat]
    exact Submodule.mem_map.mpr ⟨⁅X, w'⁆, hW_lie X w' hw', rfl⟩

/--
[continuous_map_eq_of_eq_on_kFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma continuous_map_eq_of_eq_on_kFinite
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K_sub : Subgroup G}
  [CompactSpace K_sub]
  [NormedAddCommGroup W]
  [NormedSpace ℂ W]
  {f g : F →L[ℂ] W}
-- given
  (hadm : π.IsAdmissible K_sub)
  (heq : ∀ v ∈ π.kFiniteSubspace K_sub, f v = g v) :
-- imply
  f = g := by
-- proof
  have hdense : Dense (π.kFiniteSubspace K_sub : Set F) :=
    kFiniteSubspace_dense_admissible I π K_sub hadm
  have hfun_eq : (f : F → W) = (g : F → W) :=
    Continuous.ext_on hdense f.continuous g.continuous heq
  exact ContinuousLinearMap.ext (congr_fun hfun_eq)

/--
[lie_action_preserves_invariant_subspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma lie_action_preserves_invariant_subspace
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K_sub : Subgroup G}
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
  [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
  {ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F)}
  {U : Submodule ℂ F}
  {X : 𝔤}
  {w : ↥(π.kFiniteSubspace K_sub)}
-- given
  (hadm : π.IsAdmissible K_sub)
  (hι_compat : ∀ (X : 𝔤) (w : ↥(π.kFiniteSubspace K_sub)), (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ = ι X ((π.kFiniteSubspace K_sub).subtype w))
  (hU : π.IsInvariantSubspace U)
  (hι_inv : ∀ (X : 𝔤) (v : F), v ∈ U → ι X v ∈ U)
  (hw : (π.kFiniteSubspace K_sub).subtype w ∈ U) :
-- imply
  (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ ∈ U := by
-- proof
  rw [hι_compat]
  exact hι_inv X _ hw

/--
[kFinite_dense_in_invariant_subspace_submodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma kFinite_dense_in_invariant_subspace_submodule
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [LieGroup I ⊤ G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K_sub : Subgroup G}
  [CompactSpace K_sub]
  {U : Submodule ℂ F}
-- given
  (hadm : π.IsAdmissible K_sub)
  (hU : π.IsInvariantSubspace U) :
-- imply
  let S := Submodule.map (π.kFiniteSubspace K_sub).subtype (Submodule.comap (π.kFiniteSubspace K_sub).subtype U) S.topologicalClosure = U := by
-- proof
  intro S
  apply le_antisymm
  ·
    apply S.topologicalClosure_minimal
    · intro x hx
      obtain ⟨w, hw, hwx⟩ := hx
      rwa [← hwx]
    · exact hU.isClosed
  ·
    intro v hv
    suffices hcl : v ∈ closure (S : Set F) by
      rwa [← Submodule.topologicalClosure_coe] at hcl
    obtain ⟨R, hR_kfin, hR_dirac, hR_pw⟩ :=
      ContinuousRep.measureRep_exists (π.subrepresentation U hU) K_sub
    have hdense : Dense (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U) := by
      intro w
      rw [mem_closure_iff_nhds]
      intro N hN
      rw [mem_nhds_iff] at hN
      obtain ⟨t, htN, ht_open, hw_t⟩ := hN
      have ht_nhds : t ∈ nhds w := ht_open.mem_nhds hw_t
      obtain ⟨f, hft⟩ := hR_dirac w t ht_nhds
      have ht_nhds_Rf : t ∈ nhds (R f w) := ht_open.mem_nhds hft
      obtain ⟨g, hg_kfin, hgt⟩ := hR_pw f w t ht_nhds_Rf
      exact ⟨R g w, htN hgt, hR_kfin g w hg_kfin⟩
    have kfin_subrep_to_full : ∀ (w : ↥U),
      w ∈ ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub →
      (w : F) ∈ ContinuousRep.kFiniteSubspace π K_sub := by
      intro w hw
      rw [ContinuousRep.mem_kFiniteSubspace] at hw ⊢
      unfold ContinuousRep.IsKFinite at hw ⊢
      have hmap : Submodule.map U.subtype
        (Submodule.span ℂ (Set.range (fun k : K_sub =>
          ((π.subrepresentation U hU).toMonoidHom k) w))) =
        Submodule.span ℂ (Set.range (fun k : K_sub => (π.toMonoidHom k) (w : F))) := by
        rw [Submodule.map_span]
        congr 1
        ext x
        simp only [Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, rfl⟩
        · rintro ⟨k, rfl⟩
          exact ⟨((π.subrepresentation U hU).toMonoidHom k) w, ⟨k, rfl⟩, rfl⟩
      rw [← hmap]
      exact Module.Finite.map _ U.subtype
    have image_subset : U.subtype ''
      (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U) ⊆ (S : Set F) := by
      intro x ⟨w, hw_kfin, hw_eq⟩
      have hx_kfin : x ∈ ContinuousRep.kFiniteSubspace π K_sub := by
        rw [← hw_eq]; exact kfin_subrep_to_full w hw_kfin
      have hx_U : x ∈ (U : Set F) := by
        rw [← hw_eq]; exact w.2
      exact ⟨⟨x, hx_kfin⟩, hx_U, rfl⟩
    have v_U_mem : (⟨v, hv⟩ : ↥U) ∈
      closure (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U) :=
      hdense ⟨v, hv⟩
    have hcont : Continuous (U.subtype : ↥U → F) := continuous_subtype_val
    have hv_in_closure_image : v ∈ closure (U.subtype ''
      (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U)) := by
      have := image_closure_subset_closure_image hcont ⟨⟨v, hv⟩, v_U_mem, rfl⟩
      simp only [Submodule.subtype_apply] at this
      exact this
    exact closure_mono image_subset hv_in_closure_image

/--
[kEquivariant_finiteRange_maps_to_kFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma kEquivariant_finiteRange_maps_to_kFinite
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K_sub : Subgroup G}
  {P : F →L[ℂ] F}
-- given
  (hfin : FiniteDimensional ℂ (LinearMap.range P.toLinearMap))
  (hcomm : ∀ (k : K_sub), P.comp (π.toMonoidHom k) = (π.toMonoidHom k).comp P) :
-- imply
  ∀ w, P w ∈ π.kFiniteSubspace K_sub := by
-- proof
  intro w
  show ContinuousRep.IsKFinite π K_sub (P w)
  unfold ContinuousRep.IsKFinite
  have h_in_range : ∀ k : K_sub, (π.toMonoidHom ↑k) (P w) ∈
    LinearMap.range P.toLinearMap := by
    intro k
    have heq := congr_fun (congr_arg DFunLike.coe (hcomm k)) w
    simp only [ContinuousLinearMap.comp_apply] at heq
    rw [← heq]
    exact LinearMap.mem_range.mpr ⟨(π.toMonoidHom ↑k) w, rfl⟩
  have h_span_le : Submodule.span ℂ
    (Set.range (fun k : K_sub => (π.toMonoidHom ↑k) (P w))) ≤
    LinearMap.range P.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    exact h_in_range k
  exact Module.Finite.of_injective (Submodule.inclusion h_span_le)
    (Submodule.inclusion_injective h_span_le)

/--
[finsupp_rep_intertwines](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
lemma finsupp_rep_intertwines
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup F₂]
  [NormedSpace ℂ F₂]
  [NormedAddCommGroup F₃]
  [NormedSpace ℂ F₃]
  {π₂ : ContinuousRep G F₂}
  {π₃ : ContinuousRep G F₃}
  {S : RepHom π₂ π₃}
  {K_sub : Subgroup G}
  {c : K_sub →₀ ℂ}
  {w : F₂} :
-- imply
  S.toContinuousLinearMap ((c.sum (fun k a => a • π₂.toMonoidHom k)) w) = (c.sum (fun k a => a • π₃.toMonoidHom k)) (S.toContinuousLinearMap w) := by
-- proof
  simp only [Finsupp.sum]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  rw [map_sum]
  congr 1
  ext ⟨k, hk⟩
  rw [map_smul]
  congr 1
  have := S.intertwines (k : G)
  exact congr_fun (congr_arg DFunLike.coe this) w

/--
[kFiniteSubspace_kAction_locallyFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
private lemma kFiniteSubspace_kAction_locallyFinite_eq
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K_sub : Subgroup G} :
-- imply
  (kFiniteSubspace_kAction π K_sub).IsLocallyFinite := by
-- proof
  apply kFiniteSubspace_kAction_locallyFinite π K_sub

/--
[repHom_maps_kFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HarishChandraFunctor.lean)
-/
@[path]
private lemma repHom_maps_kFinite_eq
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F₁]
  [NormedSpace ℂ F₁]
  [NormedAddCommGroup F₂]
  [NormedSpace ℂ F₂]
  {π₁ : ContinuousRep G F₁}
  {π₂ : ContinuousRep G F₂}
  {K_sub : Subgroup G}
  {T : RepHom π₁ π₂}
  {v : F₁}
-- given
  (hv : v ∈ π₁.kFiniteSubspace K_sub) :
-- imply
  T.toContinuousLinearMap v ∈ π₂.kFiniteSubspace K_sub := by
-- proof
  apply repHom_maps_kFinite π₁ π₂ K_sub T v hv


-- created on 2026-10-23

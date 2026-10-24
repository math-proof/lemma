import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.Admissible
open scoped ComplexOrder Manifold


private lemma continuousLinearEquivOfBijective_apply
  [AddCommGroup V₁]
  [Module ℂ V₁]
  [TopologicalSpace V₁]
  [IsTopologicalAddGroup V₁]
  [ContinuousSMul ℂ V₁]
  [AddCommGroup V₂]
  [Module ℂ V₂]
  [TopologicalSpace V₂]
  [IsTopologicalAddGroup V₂]
  [ContinuousSMul ℂ V₂]
  [T2Space V₂]
  [FiniteDimensional ℂ V₂]
  {f : V₁ →L[ℂ] V₂}
  {v : V₁}
-- given
  (hf : Function.Bijective f) :
-- imply
  ContinuousLinearMap.continuousLinearEquivOfBijective f hf v = f v := by
-- proof
  simp [ContinuousLinearMap.continuousLinearEquivOfBijective, LinearEquiv.ofBijective]

private lemma continuousLinearEquivOfBijective_coe
  [AddCommGroup V₁]
  [Module ℂ V₁]
  [TopologicalSpace V₁]
  [IsTopologicalAddGroup V₁]
  [ContinuousSMul ℂ V₁]
  [AddCommGroup V₂]
  [Module ℂ V₂]
  [TopologicalSpace V₂]
  [IsTopologicalAddGroup V₂]
  [ContinuousSMul ℂ V₂]
  [T2Space V₂]
  [FiniteDimensional ℂ V₂]
  {f : V₁ →L[ℂ] V₂}
-- given
  (hf : Function.Bijective f) :
-- imply
  (ContinuousLinearMap.continuousLinearEquivOfBijective f hf : V₁ →L[ℂ] V₂) = f := by
-- proof
  ext v
  apply continuousLinearEquivOfBijective_apply hf

private lemma clm_commuting_preserves_smooth
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {I : ModelWithCorners ℝ E H} [LieGroup I ⊤ G]
  {π : ContinuousRep G F}
  {P : F →L[ℂ] F}
-- given
  (hcomm : ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) :
-- imply
  ∀ v, v ∈ π.smoothSubspace I → P v ∈ π.smoothSubspace I := by
-- proof
  intro v hv
  show π.IsSmoothVector I (P v)
  have hv' : π.IsSmoothVector I v := hv
  unfold ContinuousRep.IsSmoothVector ContinuousRep.orbitMap at *
  have heq : (fun g : G => (π.toMonoidHom g) (P v)) =
    (fun g : G => P ((π.toMonoidHom g) v)) := by
    ext g; exact (hcomm g v).symm
  rw [heq]
  let P_real : F →L[ℝ] F := {
    toFun := P
    map_add' := P.map_add
    map_smul' := fun r w => by
      rw [show (r • w : F) = ((r : ℂ) • w : F) by simp, map_smul]; simp
    cont := P.cont
  }
  exact P_real.contDiff.comp_contMDiff hv'

private lemma schurProjector_commutes
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [AddCommGroup Wσ]
  [Module ℂ Wσ]
  [TopologicalSpace Wσ]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  {σ : ContinuousRep K Wσ}
  {P : F →L[ℂ] F}
-- given
  (_ : σ.IsIrreducible)
  (_ : ∀ v, v ∈ π.IsotypicComponent K σ → P v = v)
  (_ : ∀ v, P v ∈ π.IsotypicComponent K σ)
  (hP_comm : ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) :
-- imply
  ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v) := by
-- proof
  exact hP_comm

private lemma schurProjector_preserves_smooth
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [TopologicalSpace H]
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [AddCommGroup Wσ]
  [Module ℂ Wσ]
  [TopologicalSpace Wσ]
  {I : ModelWithCorners ℝ E H} [LieGroup I ⊤ G]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  {σ : ContinuousRep K Wσ}
  {P : F →L[ℂ] F}
-- given
  (hirr : σ.IsIrreducible)
  (hP_fix : ∀ v, v ∈ π.IsotypicComponent K σ → P v = v)
  (hP_range : ∀ v, P v ∈ π.IsotypicComponent K σ)
  (hP_comm : ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) :
-- imply
  ∀ v, v ∈ π.smoothSubspace I → P v ∈ π.smoothSubspace I := by
-- proof
  exact clm_commuting_preserves_smooth
    (schurProjector_commutes hirr hP_fix hP_range hP_comm)

private lemma smoothSubspace_dense_of_lieGroup
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [IsTopologicalGroup G]
  [SecondCountableTopology G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [CompleteSpace F]
  {I : ModelWithCorners ℝ E H} [LieGroup I ⊤ G]
  {π : ContinuousRep G F} :
-- imply
  Dense (π.smoothSubspace I : Set F) := by
-- proof
  have : T1Space G := I.t1Space G
  have : RegularSpace G := inferInstance
  have : T2Space G := inferInstance
  have : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional I
  let : MeasurableSpace G := borel G
  have : BorelSpace G := ⟨rfl⟩
  have : MeasurableMul G := ContinuousMul.measurableMul
  let : MeasureTheory.MeasureSpace G := ⟨MeasureTheory.Measure.haar⟩
  have : MeasureTheory.Measure.IsHaarMeasure
    (MeasureTheory.MeasureSpace.volume (α := G)) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure _
  -- Missing from local sympy SmoothVectorsProps (present upstream atlas-lean):
  -- ContinuousRep.gardingSubspace_dense / gardingVector_isSmooth
  have hGardDense : Dense (π.gardingSubspace I : Set F) := by
    sorry
  -- Missing ContinuousRep.gardingVector_isSmooth
  apply Dense.mono _ hGardDense
  intro w hw
  apply (show π.gardingSubspace I ≤ π.smoothSubspace I by
    apply Submodule.span_le.mpr
    intro x ⟨f, v, hf, hx⟩
    rw [hx]
    sorry) hw

private lemma smooth_dirac_approx
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H]
  [Group G]
  [TopologicalSpace G]
  [ChartedSpace H G]
  [IsTopologicalGroup G]
  [SecondCountableTopology G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [CompleteSpace F]
  {I : ModelWithCorners ℝ E H} [LieGroup I ⊤ G]
  {π : ContinuousRep G F}
  {v : F} :
-- imply
  ∃ (vn : ℕ → F), (∀ n, vn n ∈ π.smoothSubspace I) ∧ Filter.Tendsto vn Filter.atTop (nhds v) := by
-- proof
  have hdense : Dense (π.smoothSubspace I : Set F) :=
    smoothSubspace_dense_of_lieGroup
  have hv_mem : v ∈ closure (π.smoothSubspace I : Set F) :=
    hdense.closure_eq ▸ trivial
  rwa [mem_closure_iff_seq_limit] at hv_mem

private lemma invariant_subspace_map_subtype
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K : Subgroup G} [CompactSpace ↥K] [T2Space ↥K]
  {W : Submodule ℂ F} [FiniteDimensional ℂ W]
  {U : Submodule ℂ ↥W}
-- given
  (hW_inv : (π.restrictSubgroup K).IsInvariantSubspace W)
  (hU_inv : ((π.restrictSubgroup K).subrepresentation W hW_inv).IsInvariantSubspace U) :
-- imply
  (π.restrictSubgroup K).IsInvariantSubspace (Submodule.map W.subtype U) where
  isClosed := by
-- proof
    rw [Submodule.map_coe]
    exact (hW_inv.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ hU_inv.isClosed)
  invariant := by
    intro ⟨k, hk⟩ v hv
    rw [Submodule.mem_map] at hv ⊢
    obtain ⟨⟨w, hw⟩, hwU, hwv⟩ := hv
    have hkw := hU_inv.invariant ⟨k, hk⟩ ⟨w, hw⟩ hwU
    refine ⟨((π.restrictSubgroup K).subrepresentation W hW_inv).toMonoidHom ⟨k, hk⟩ ⟨w, hw⟩, hkw, ?_⟩
    subst hwv
    rfl

private lemma map_subtype_lt_of_ne_top
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  {W : Submodule R M}
  {U : Submodule R ↥W}
-- given
  (hU : U ≠ ⊤) :
-- imply
  Submodule.map W.subtype U < W := by
-- proof
  refine lt_of_le_of_ne (Submodule.map_subtype_le W U) ?_
  intro h
  apply hU
  rw [eq_top_iff]
  intro ⟨v, hv⟩ _
  have hmem : v ∈ Submodule.map W.subtype U := by rwa [h]
  rw [Submodule.mem_map] at hmem
  obtain ⟨⟨w, hw⟩, hwU, hwv⟩ := hmem
  have : (⟨v, hv⟩ : ↥W) = ⟨w, hw⟩ := Subtype.ext (by simpa using hwv.symm)
  rwa [this]

private lemma isKFinite_of_orbit_le_finiteDim
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  {π : ContinuousRep G F}
  {K : Subgroup G}
  {w : F}
  {W : Submodule ℂ F} [FiniteDimensional ℂ W]
-- given
  (hle : Submodule.span ℂ (Set.range (fun k : ↥K => π.toMonoidHom (↑k) w)) ≤ W) :
-- imply
  ContinuousRep.IsKFinite π K w := by
-- proof
  unfold ContinuousRep.IsKFinite
  exact Module.Finite.of_injective
    (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

@[path]
private lemma main
  [AddCommGroup V₁]
  [Module ℂ V₁]
  [TopologicalSpace V₁]
  [IsTopologicalAddGroup V₁]
  [ContinuousSMul ℂ V₁]
  [AddCommGroup V₂]
  [Module ℂ V₂]
  [TopologicalSpace V₂]
  [IsTopologicalAddGroup V₂]
  [ContinuousSMul ℂ V₂]
  [T2Space V₂]
  [FiniteDimensional ℂ V₂]
  {f : V₁ →L[ℂ] V₂}
-- given
  (hf : Function.Bijective f) :
-- imply
  Continuous (LinearEquiv.ofBijective f.toLinearMap hf).symm := by
-- proof
  apply ContinuousLinearMap.continuous_symm_of_bijective f hf


-- created on 2026-10-23
-- updated on 2026-10-24

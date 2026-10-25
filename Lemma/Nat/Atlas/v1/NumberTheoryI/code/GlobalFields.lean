import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.NumberTheoryI.code.GlobalFields
open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain AbsoluteValue
open Polynomial UniqueFactorizationMonoid Classical


namespace AbsoluteValue

/--
[IsTrivial.map_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma IsTrivial.map_ne_zero
  [Field K]
  {v : AbsoluteValue K ℝ}
  {x : K}
-- given
  (hv : v.IsTrivial)
  (hx : x ≠ 0) :
-- imply
  v x = 1 :=
-- proof
  hv x hx

end AbsoluteValue

namespace AbsoluteValue

/--
[IsTrivial.of_isEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma IsTrivial.of_isEquiv
  [Field K]
  {v w : AbsoluteValue K ℝ}
-- given
  (hv : v.IsTrivial)
  (h : v.IsEquiv w) :
-- imply
  w.IsTrivial := by
-- proof
  intro x hx
  have h0 : v x = v 1 := by rw [hv x hx, map_one]
  have h1 := h.eq_iff_eq.mp h0
  rwa [map_one] at h1
end AbsoluteValue
section Place


/--
[theorem_13_5_dense_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma theorem_13_5_dense_embedding
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  DenseRange (algebraMap K ((v : NumberField.InfinitePlace K) → WithAbs v.1)) :=
-- proof
  denseRange_algebraMap_pi K

/--
[completionEmbedding_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma completionEmbedding_continuous
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : NumberField.InfinitePlace K}
  {w : NumberField.InfinitePlace L}
-- given
  (hw : w.comap (algebraMap K L) = v) :
-- imply
  Continuous (completionEmbedding v w hw) := by
-- proof
  simp only [completionEmbedding, Isometry.mapRingHom, UniformSpace.Completion.mapRingHom]
  exact UniformSpace.Completion.continuous_extension
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in

/--
[canonicalMap_surjective_hfd_tgt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma canonicalMap_surjective_hfd_tgt
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : NumberField.InfinitePlace K} :
-- imply
  @FiniteDimensional v.Completion ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) _ _ (@Pi.module { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v } (fun w => w.val.Completion) v.Completion _ _ (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)) := by
-- proof
  have h_fin : ∀ (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }),
    @Module.Finite v.Completion w.val.Completion _ _
      (completionEmbedding v w.val w.prop).toAlgebra.toModule := by
    intro w
    letI myAlg : Algebra v.Completion w.val.Completion :=
      (completionEmbedding v w.val w.prop).toAlgebra
    letI mySMul : SMul v.Completion w.val.Completion := myAlg.toSMul
    haveI : ContinuousMul w.val.Completion :=
      (inferInstance : IsTopologicalRing w.val.Completion).toContinuousMul
    haveI : @ContinuousSMul v.Completion w.val.Completion mySMul _ _ := by
      refine ⟨?_⟩
      show Continuous (fun p : v.Completion × w.val.Completion =>
        completionEmbedding v w.val w.prop p.1 * p.2)
      exact ((completionEmbedding_continuous v w.val w.prop).comp continuous_fst).mul continuous_snd
    exact @FiniteDimensional.of_locallyCompactSpace v.Completion _ _ w.val.Completion _ _ _ _
      myAlg.toModule this _
  exact @Module.Finite.pi v.Completion _
    { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }
    (fun w => w.val.Completion) _
    (fun w => inferInstance)
    (fun w => (completionEmbedding v w.val w.prop).toAlgebra.toModule)
    h_fin

/--
[canonicalMap_tmul_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma canonicalMap_tmul_one
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : NumberField.InfinitePlace K}
  {l : L}
-- given
  (w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) :
-- imply
  (canonicalMap (L := L) v) (l ⊗ₜ[K] 1) w = algebraMap L w.val.Completion l := by
-- proof
  simp only [canonicalMap, Pi.algHom_apply,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, algebraMapLToCompletion]
  exact mul_one _
set_option maxHeartbeats 8000000

/--
[prop_4_36_tensorProduct_finite_isSemisimpleRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma prop_4_36_tensorProduct_finite_isSemisimpleRing
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  IsSemisimpleRing (TensorProduct K L (v.adicCompletion K)) := by
-- proof
  haveI : Algebra.Unramified K L :=
    ⟨Algebra.FormallyUnramified.of_isSeparable K L, inferInstance⟩
  haveI := (Algebra.Unramified.baseChange K L (v.adicCompletion K)).formallyUnramified
  haveI : IsReduced (TensorProduct K (v.adicCompletion K) L) :=
    Algebra.FormallyUnramified.isReduced_of_field (v.adicCompletion K) _
  haveI : IsArtinianRing (TensorProduct K (v.adicCompletion K) L) :=
    IsArtinianRing.of_finite (v.adicCompletion K) _
  haveI : IsSemisimpleRing (TensorProduct K (v.adicCompletion K) L) :=
    @IsArtinianRing.isSemisimpleRing_of_isReduced _ _ _ _
  exact (Algebra.TensorProduct.comm K L (v.adicCompletion K)).toRingEquiv.symm.isSemisimpleRing

/--
[finitePlacesAbove_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma finitePlacesAbove_finite
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  Finite { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } := by
-- proof
  haveI := v.isMaximal
  apply Finite.of_injective
    (fun ⟨w, hw⟩ => (⟨w.asIdeal, w.isPrime, ⟨hw.symm⟩⟩ : Ideal.primesOver v.asIdeal (𝓞 L)))
  intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
  simp only [Subtype.mk.injEq] at h
  exact Subtype.ext (HeightOneSpectrum.ext_iff.mpr h)

/--
[prop_10_3_10_4_finiteDimensional_completion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma prop_10_3_10_4_finiteDimensional_completion
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)}
-- given
  (hw : FinitePlace.LiesAbove w v) :
-- imply
  letI := (completionEmbedding_finite v w hw).toAlgebra FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) := by
-- proof
  letI := (completionEmbedding_finite v w hw).toAlgebra
  haveI : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
    apply continuousSMul_of_algebraMap
    show Continuous (completionEmbedding_finite v w hw).toRingHom
    exact UniformSpace.Completion.continuous_extension
  haveI : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    change algebraMap K (w.adicCompletion L) x =
      (completionEmbedding_finite v w hw) (algebraMap K (v.adicCompletion K) x)
    rw [AlgHom.commutes]
  exact inferInstance

/--
[thm_11_23_4_local_degree_ef](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma thm_11_23_4_local_degree_ef
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)}
  [Algebra (v.adicCompletion K) (w.adicCompletion L)]
  [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]
-- given
  (hw : FinitePlace.LiesAbove w v) :
-- imply
  Module.finrank (v.adicCompletion K) (w.adicCompletion L) = Ideal.ramificationIdx v.asIdeal w.asIdeal * Ideal.inertiaDeg v.asIdeal w.asIdeal := by
-- proof
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  exact KroneckerWeber.thm_11_23_part4_completion_degree_eq_ef
    (𝓞 K) K L (𝓞 L) v w

/--
[thm_5_35_11_23_degree_identity_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma thm_5_35_11_23_degree_identity_finrank
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  {v : HeightOneSpectrum (𝓞 K)}
  [Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }]
-- given
  (instAlg : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), Algebra (v.adicCompletion K) (w.val.adicCompletion L))
  (instST : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), @IsScalarTower K (v.adicCompletion K) (w.val.adicCompletion L) _ (instAlg w).toSMul _) :
-- imply
  Module.finrank K L = ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }, @Module.finrank (v.adicCompletion K) (w.val.adicCompletion L) _ _ (instAlg w).toModule := by
-- proof
  have h_ef : ∀ (ww : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
    @Module.finrank (v.adicCompletion K) (ww.val.adicCompletion L) _ _
      (instAlg ww).toModule =
    Ideal.ramificationIdx v.asIdeal ww.val.asIdeal *
    Ideal.inertiaDeg v.asIdeal ww.val.asIdeal := by
    intro ⟨w, hw⟩
    exact @thm_11_23_4_local_degree_ef K L _ _ _ _ _ _ _ v w hw
      (instAlg ⟨w, hw⟩) (instST ⟨w, hw⟩)
  simp_rw [h_ef]
  classical
  haveI : v.asIdeal.IsMaximal := v.isMaximal
  rw [← Ideal.sum_ramification_inertia (𝓞 L) K L v.ne_bot]
  symm
  apply Finset.sum_nbij
    (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) => w.val.asIdeal)
  ·
    intro ⟨w, hw⟩ _
    rw [mem_primesOverFinset_iff v.ne_bot]
    exact ⟨w.isPrime, ⟨(show FinitePlace.LiesAbove w v from hw).symm⟩⟩
  ·
    intro ⟨w₁, _⟩ _ ⟨w₂, _⟩ _ h
    simp only [Subtype.mk.injEq]
    exact HeightOneSpectrum.ext h
  ·
    intro P hP
    simp only [Finset.coe_univ, Set.mem_univ, Finset.mem_coe, Set.mem_image, true_and] at hP ⊢
    rw [mem_primesOverFinset_iff v.ne_bot] at hP
    have hne : P ≠ ⊥ := by
      intro h; rw [h] at hP
      have := hP.2.over
      simp only [Ideal.under] at this
      rw [Ideal.comap_bot_of_injective _
        (algebraMap_injective_of_field_isFractionRing (𝓞 K) (𝓞 L) K L)] at this
      exact v.ne_bot this
    exact ⟨⟨⟨P, hP.1, hne⟩, (show FinitePlace.LiesAbove ⟨P, hP.1, hne⟩ v from hP.2.over.symm)⟩, rfl⟩
  ·
    intro _ _; rfl

/--
[prop_10_3_10_4_finrank_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma prop_10_3_10_4_finrank_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  letI : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) := Algebra.TensorProduct.rightAlgebra letI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), Module (v.adicCompletion K) (w.val.adicCompletion L) :=
-- proof
  fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule
  Module.finrank (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) =
  Module.finrank (v.adicCompletion K)
    ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
      w.val.adicCompletion L) := by
  letI instSrc : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  letI instTgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
    Algebra (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra
  haveI hfin : Finite { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } :=
    finitePlacesAbove_finite v
  haveI : Fintype { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v } :=
    Fintype.ofFinite _
  haveI instFD : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
    @FiniteDimensional (v.adicCompletion K) (w.val.adicCompletion L) _ _ (instTgt w).toModule :=
    fun w => prop_10_3_10_4_finiteDimensional_completion v w.val w.prop
  haveI instFree : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
    @Module.Free (v.adicCompletion K) (w.val.adicCompletion L) _ _ (instTgt w).toModule :=
    fun w => @Module.Free.of_divisionRing _ _ _ _ (instTgt w).toModule
  have h_lhs : Module.finrank (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) =
    Module.finrank K L := by
    have := LinearEquiv.finrank_eq
      (Algebra.TensorProduct.commRight K (v.adicCompletion K) L).symm.toLinearEquiv
    rw [this]
    exact Module.finrank_baseChange ..
  have h_rhs : Module.finrank (v.adicCompletion K)
    ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
      w.val.adicCompletion L) =
    ∑ w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v },
      Module.finrank (v.adicCompletion K) (w.val.adicCompletion L) :=
    Module.finrank_pi_fintype (v.adicCompletion K)
  have instSTgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
    @IsScalarTower K (v.adicCompletion K) (w.val.adicCompletion L) _
      (instTgt w).toSMul _ :=
    fun w => IsScalarTower.of_algHom (completionEmbedding_finite v w.val w.prop)
  have h_bridge := thm_5_35_11_23_degree_identity_finrank (L := L) v instTgt instSTgt
  linarith

/--
[canonicalMap_finite_isKvLinear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma canonicalMap_finite_isKvLinear
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)} :
-- imply
  letI : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) := Algebra.TensorProduct.rightAlgebra letI : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }), Module (v.adicCompletion K) (w.val.adicCompletion L) :=
-- proof
  fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule
  ∃ f : TensorProduct K L (v.adicCompletion K) →ₗ[v.adicCompletion K]
    ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
      w.val.adicCompletion L),
    (∀ x, f x = (canonicalMap_finite (L := L) v) x) := by
  letI instSrc : Algebra (v.adicCompletion K) (TensorProduct K L (v.adicCompletion K)) :=
    Algebra.TensorProduct.rightAlgebra
  letI instTgt : ∀ (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }),
    Module (v.adicCompletion K) (w.val.adicCompletion L) :=
    fun w => (completionEmbedding_finite v w.val w.prop).toAlgebra.toModule
  letI instPiMod : Module (v.adicCompletion K)
    ((w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) →
      w.val.adicCompletion L) :=
    @Pi.module _ (fun (w : { w : HeightOneSpectrum (𝓞 L) // FinitePlace.LiesAbove w v }) =>
      w.val.adicCompletion L) (v.adicCompletion K) _ _ instTgt
  have hsmul : ∀ (c : v.adicCompletion K) (x : TensorProduct K L (v.adicCompletion K)),
    (canonicalMap_finite (L := L) v) (c • x) =
      @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * 0) = _
      rw [mul_zero, map_zero]
      exact (@smul_zero _ _ _
        instPiMod.toDistribMulAction.toDistribSMul.toSMulZeroClass c).symm
    | tmul l y =>
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * (l ⊗ₜ y)) = _
      simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      ext ⟨w, hw⟩
      simp only [canonicalMap_finite, Pi.algHom_apply,
        Algebra.TensorProduct.productMap_apply_tmul, map_mul]
      exact mul_left_comm _ _ _
    | add a b ha hb =>
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * (a + b)) =
        @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) (a + b))
      rw [mul_add, map_add, map_add]
      change (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * a) +
        (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * b) =
        @SMul.smul _ _ instPiMod.toSMul c
          ((canonicalMap_finite (L := L) v) a + (canonicalMap_finite (L := L) v) b)
      rw [show (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * a) =
        @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) a) from ha,
        show (canonicalMap_finite (L := L) v) ((1 ⊗ₜ c) * b) =
        @SMul.smul _ _ instPiMod.toSMul c ((canonicalMap_finite (L := L) v) b) from hb]
      exact (@smul_add _ _ _
        instPiMod.toDistribMulAction.toDistribSMul c
        ((canonicalMap_finite v) a) ((canonicalMap_finite v) b)).symm
  exact ⟨{ toFun := canonicalMap_finite v
    map_add' := (canonicalMap_finite v).map_add
    map_smul' := hsmul }, fun _ => rfl⟩

/--
[completion_real_ringEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma completion_real_ringEquiv
  [Field K]
  {w : NumberField.InfinitePlace K}
-- given
  (hw : w.IsReal) :
-- imply
  Nonempty (w.Completion ≃+* ℝ) :=
-- proof
  ⟨NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw⟩

/--
[completion_complex_ringEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma completion_complex_ringEquiv
  [Field K]
  {w : NumberField.InfinitePlace K}
-- given
  (hw : w.IsComplex) :
-- imply
  Nonempty (w.Completion ≃+* ℂ) :=
-- proof
  ⟨NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hw⟩
section IrreducibleFactorsAndPlaces
open Polynomial UniqueFactorizationMonoid Classical

/--
[corollary_13_6_factor_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma corollary_13_6_factor_count
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  Fintype.card (NumberField.InfinitePlace K) = nrRealPlaces K + nrComplexPlaces K :=
-- proof
  card_eq_nrRealPlaces_add_nrComplexPlaces K
end IrreducibleFactorsAndPlaces
section GaloisOrbitsAndPlaces

/--
[corollary_13_7_mem_orbit_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma corollary_13_7_mem_orbit_iff
  [Field k]
  [Field K]
  [Algebra k K]
  [IsGalois k K]
  {w w' : NumberField.InfinitePlace K} :
-- imply
  w' ∈ MulAction.orbit (K ≃ₐ[k] K) w ↔ w.comap (algebraMap k K) = w'.comap (algebraMap k K) :=
-- proof
  InfinitePlace.mem_orbit_iff

/--
[corollary_13_7_exists_smul_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma corollary_13_7_exists_smul_eq
  [Field k]
  [Field K]
  [Algebra k K]
  [IsGalois k K]
  {w w' : NumberField.InfinitePlace K}
-- given
  (h : w.comap (algebraMap k K) = w'.comap (algebraMap k K)) :
-- imply
  ∃ σ : K ≃ₐ[k] K, σ • w = w' :=
-- proof
  InfinitePlace.exists_smul_eq_of_comap_eq h

/--
[corollary_13_7_comap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma corollary_13_7_comap_surjective
  {k K : Type*}
  [Field k]
  [Field K]
  [Algebra k K]
  [Algebra.IsAlgebraic k K] :
-- imply
  Function.Surjective (InfinitePlace.comap · (algebraMap k K) : InfinitePlace K → InfinitePlace k) :=
-- proof
  InfinitePlace.comap_surjective

/--
[corollary_13_7_mk_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma corollary_13_7_mk_eq_iff
  [Field K]
  {φ ψ : K →+* ℂ} :
-- imply
  InfinitePlace.mk φ = InfinitePlace.mk ψ ↔ φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ :=
-- proof
  InfinitePlace.mk_eq_iff

/--
[place_isReal_or_isComplex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma place_isReal_or_isComplex
  [Field K]
  {w : NumberField.InfinitePlace K} :
-- imply
  w.IsReal ∨ w.IsComplex :=
-- proof
  InfinitePlace.isReal_or_isComplex w

/--
[ComplexEmbedding.conjugateSetoid_rel_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma ComplexEmbedding.conjugateSetoid_rel_iff
  [Field L]
  {φ ψ : L →+* ℂ} :
-- imply
  (ComplexEmbedding.conjugateSetoid L).r φ ψ ↔ (φ = ψ ∨ ComplexEmbedding.conjugate φ = ψ) :=
-- proof
  mk_eq_iff

/--
[isRealEmbedding_iff_isReal_place](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma isRealEmbedding_iff_isReal_place
  [Field K]
  {φ : K →+* ℂ} :
-- imply
  IsRealEmbedding φ ↔ (InfinitePlace.mk φ).IsReal := by
-- proof
  constructor
  · intro h
    exact ⟨φ, h, rfl⟩
  · intro h
    exact InfinitePlace.isReal_of_mk_isReal h

/--
[isComplexEmbedding_iff_isComplex_place](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma isComplexEmbedding_iff_isComplex_place
  [Field K]
  {φ : K →+* ℂ} :
-- imply
  IsComplexEmbedding φ ↔ (InfinitePlace.mk φ).IsComplex := by
-- proof
  rw [IsComplexEmbedding, ← InfinitePlace.not_isReal_iff_isComplex]
  exact not_congr isRealEmbedding_iff_isReal_place
section DegreeFormula

/--
[corollary_13_9](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma corollary_13_9
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  nrRealPlaces K + 2 * nrComplexPlaces K = finrank ℚ K :=
-- proof
  card_add_two_mul_card_eq_rank K

/--
[card_complex_embeddings_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma card_complex_embeddings_eq
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  card { φ : K →+* ℂ // ¬ComplexEmbedding.IsReal φ } = 2 * nrComplexPlaces K :=
-- proof
  card_complex_embeddings K

/--
[card_real_embeddings_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma card_real_embeddings_eq
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  card { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } = nrRealPlaces K :=
-- proof
  card_real_embeddings K
end DegreeFormula
section DiscriminantSign

/--
[proposition_13_11](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma proposition_13_11
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  (NumberField.discr K).sign = (-1) ^ nrComplexPlaces K :=
-- proof
  NumberField.sign_discr K

/--
[discr_ne_zero'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
lemma discr_ne_zero'
  {K : Type*}
  [Field K]
  [NumberField K] :
-- imply
  NumberField.discr K ≠ 0 :=
-- proof
  NumberField.discr_ne_zero K
end DiscriminantSign
alias tensorProductDecomp_denseRange := theorem_13_5_dense_embedding
alias tensorProductDecomp_infinitePlace := theorem_13_5_tensor_product_iso
alias tensorProductDecomp_infinitePlace_Kv := theorem_13_5_tensor_product_iso_Kv
alias tensorProductDecomp_finitePlace := theorem_13_5_finite_place
alias tensorProductDecomp_finitePlace_Kv := theorem_13_5_finite_place_Kv
alias infinitePlace_card_eq_real_add_complex := corollary_13_6_factor_count
alias irredFactors_card_eq_infinitePlace_card := corollary_13_6_irred_factors
alias placesAboveReal_card_eq_irredFactors := corollary_13_6_places_above_real
alias placesAboveComplex_card_eq_finrank := corollary_13_6_places_above_complex
alias placesAboveFinite_equiv_irredFactors := corollary_13_6_places_above_finite
alias completionIso_finitePlace_adjoinRoot := corollary_13_6_completion_iso_finite
alias galoisOrbit_infinitePlace_equiv := corollary_13_7_orbit_equiv
alias infinitePlace_mem_orbit_iff_comap_eq := corollary_13_7_mem_orbit_iff
alias infinitePlace_exists_smul_eq_of_comap_eq := corollary_13_7_exists_smul_eq
alias infinitePlace_comap_surjective := corollary_13_7_comap_surjective
alias infinitePlace_mk_eq_iff_conjugate := corollary_13_7_mk_eq_iff
alias conjugateOrbit_equiv_infinitePlace := corollary_13_7_embedding_orbit_equiv_Q
alias conjugateOrbitAbove_equiv_placesAbove := corollary_13_7_embeddings_equiv
alias nrRealPlaces_add_two_nrComplexPlaces_eq_finrank := corollary_13_9
alias discr_sign_eq_neg_one_pow_nrComplexPlaces := proposition_13_11
alias tensorProduct_isSemisimpleRing_finitePlace := prop_4_36_tensorProduct_finite_isSemisimpleRing
alias completionEmbedding_finiteDimensional := prop_10_3_10_4_finiteDimensional_completion
alias finrank_tensorProduct_eq_finrank_completionProd := prop_10_3_10_4_finrank_eq
alias localDegree_eq_ramificationIdx_mul_inertiaDeg := thm_11_23_4_local_degree_ef
alias finrank_eq_sum_localDegrees := thm_5_35_11_23_degree_identity_finrank
alias canonicalMap_finite_ker_no_nonzero_idempotent := cor_4_32_no_nonzero_idempotent_in_ker_finite
alias completionProd_finiteDimensional_infinitePlace := canonicalMap_surjective_hfd_tgt
alias finrank_tensorProduct_eq_finrank_completionProd_infinite := canonicalMap_surjective_hdim
alias finrank_eq_sum_localDegrees_infinite := degree_identity_infinite_finrank
alias canonicalMap_finite_completionLinear := canonicalMap_finite_isKvLinear
end

/--
[multiplicative_toAdd_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
private lemma multiplicative_toAdd_pow_eq
  {e : ℕ}
-- given
  (h : Multiplicative ℤ) :
-- imply
  Multiplicative.toAdd (h ^ e) = e * Multiplicative.toAdd h := by
-- proof
  apply multiplicative_toAdd_pow h e

/--
[exists_pow_lt_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
private lemma exists_pow_lt_of_ne_zero_eq
  {m : WithZero (Multiplicative ℤ)}
  {e : ℕ}
-- given
  (hm : m ≠ 0)
  (he : e ≠ 0) :
-- imply
  ∃ d : WithZero (Multiplicative ℤ), d ≠ 0 ∧ ∀ a : WithZero (Multiplicative ℤ), a < d → a ^ e < m := by
-- proof
  apply exists_pow_lt_of_ne_zero m hm e he

/--
[algebraMap_withVal_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
private lemma algebraMap_withVal_continuous_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)}
-- given
  (hw : FinitePlace.LiesAbove w v) :
-- imply
  Continuous ((WithVal.equiv (w.valuation L)).symm.toRingHom.comp ((algebraMap K L).comp (WithVal.equiv (v.valuation K)).toRingHom) : WithVal (v.valuation K) →+* WithVal (w.valuation L)) := by
-- proof
  apply algebraMap_withVal_continuous v w hw

/--
[completionEmbedding_finite_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean)
-/
@[path]
private lemma completionEmbedding_finite_continuous_eq
  [Field K]
  [Field L]
  [NumberField K]
  [NumberField L]
  [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}
  {w : HeightOneSpectrum (𝓞 L)}
-- given
  (hw : FinitePlace.LiesAbove w v) :
-- imply
  Continuous (completionEmbedding_finite_ringHom v w) := by
-- proof
  apply completionEmbedding_finite_continuous v w hw


-- created on 2026-10-23

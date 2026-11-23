module

public import Mathlib
public import Theorem.Matrix.FactorizableTestFn
public import Abbrev.AutomorphicForm_LocalOrbitalBase

public noncomputable section

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

noncomputable section

namespace AutomorphicForm

section IntegralUnits

variable {A : Type*}


public theorem integralMatrixSet_eq_pi (U : Set A) :
    integralMatrixSet U = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => U := by
  ext m
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩


public theorem isCompact_integralMatrixSet [TopologicalSpace A] {U : Set A} (hU : IsCompact U) :
    IsCompact (integralMatrixSet U) := by
  rw [integralMatrixSet_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hU


public theorem isOpen_integralMatrixSet [TopologicalSpace A] {U : Set A} (hU : IsOpen U) : IsOpen (integralMatrixSet U) := by
  rw [integralMatrixSet_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hU

variable [CommRing A]


public theorem mem_integralUnitsSet {U : Set A} {g : GL (Fin 2) A} :
    g ∈ integralUnitsSet U ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) A) i j ∈ U) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j ∈ U :=
  Iff.rfl


public theorem one_mem_integralUnitsSet {U : Set A} (h0 : (0 : A) ∈ U) (h1 : (1 : A) ∈ U) :
    (1 : GL (Fin 2) A) ∈ integralUnitsSet U := by
  have hmat : (1 : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U := fun i j => by
    by_cases h : i = j
    · subst h; rw [Matrix.one_apply_eq]; exact h1
    · rw [Matrix.one_apply_ne h]; exact h0
  refine ⟨?_, ?_⟩
  · rw [Units.val_one]; exact hmat
  · rw [inv_one, Units.val_one]; exact hmat


public theorem integralUnitsSet_eq_preimage (U : Set A) :
    integralUnitsSet U = (Units.embedProduct (Matrix (Fin 2) (Fin 2) A)) ⁻¹'
      (integralMatrixSet U ×ˢ (MulOpposite.op '' integralMatrixSet U)) := by
  ext g
  simp only [integralUnitsSet, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := MulOpposite.op_injective hm'
    rw [← this]
    exact hm


public theorem isCompact_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {U : Set A}
    (hU : IsCompact U) :
    IsCompact (integralUnitsSet U) := by
  rw [integralUnitsSet_eq_preimage]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_integralMatrixSet hU).prod
      ((isCompact_integralMatrixSet hU).image MulOpposite.continuous_op))


public theorem isOpen_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {U : Set A}
    (hU : IsOpen U) : IsOpen (integralUnitsSet U) := by
  rw [integralUnitsSet_eq_preimage]
  exact ((isOpen_integralMatrixSet hU).prod
    (MulOpposite.opHomeomorph.isOpenMap _ (isOpen_integralMatrixSet hU))).preimage
    Units.continuous_embedProduct

end IntegralUnits

section Local

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))


public theorem isLocalTestFn_zero : IsLocalTestFn K v (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩


public theorem continuous_localAt : Continuous (localAt K v) :=
  (AdelicLevel.continuous_finComponent (𝓞 K) K v).comp (AdelicLevel.continuous_glFin (𝓞 K) K)


public theorem mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)} :
    g ∈ localIntegralSet K v ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K :=
  Iff.rfl


public theorem one_mem_localIntegralSet : (1 : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v :=
  one_mem_integralUnitsSet (zero_mem _) (one_mem _)


public theorem isCompact_localIntegralSet : IsCompact (localIntegralSet K v) :=
  isCompact_integralUnitsSet
    (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v))


public theorem isOpen_localIntegralSet : IsOpen (localIntegralSet K v) :=
  isOpen_integralUnitsSet ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v)


public theorem coe_localIntegralCompacts :
    (localIntegralCompacts K v : Set (GL (Fin 2) (v.adicCompletion K))) = localIntegralSet K v :=
  rfl


public theorem isLocallyConstant_indicator_one {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsOpen U) (hU' : IsClosed U) : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) := by
  intro s
  by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = Set.univ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact isOpen_univ
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = U := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact hU
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = Uᶜ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact hU'.isOpen_compl
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = ∅ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact isOpen_empty


public theorem isLocalTestFn_indicator_localIntegralSet :
    IsLocalTestFn K v ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_localIntegralSet K v)
      (isCompact_localIntegralSet K v).isClosed,
    HasCompactSupport.intro (isCompact_localIntegralSet K v) fun _ hg => by simp [hg]⟩


public theorem borelSpace_localGLBorel :
    @BorelSpace (GL (Fin 2) (v.adicCompletion K)) _ (localGLBorel K v) :=
  @BorelSpace.mk _ _ (localGLBorel K v) rfl


public theorem locallyCompactSpace_matrix_adicCompletion :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → v.adicCompletion K))


public theorem locallyCompactSpace_localGL : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) := by
  haveI := locallyCompactSpace_matrix_adicCompletion K v
  infer_instance


public theorem isHaarMeasure_localHaar :
    @Measure.IsHaarMeasure (GL (Fin 2) (v.adicCompletion K)) _ _ (localGLBorel K v) (localHaar K v) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.isHaarMeasure_haarMeasure _


public theorem localHaar_localIntegralSet : localHaar K v (localIntegralSet K v) = 1 := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.haarMeasure_self

end Local

section OrbitalIntegral

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))


public theorem isSectionFn_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsSectionFn K v γ τ (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩


public theorem isOrbitalIntegral_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsOrbitalIntegral K v γ τ (fun _ => 0) 0 :=
  ⟨fun _ => 0, isSectionFn_zero K v γ τ, by simp⟩


public theorem not_isOrbitalIntegral_zero_one (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    ¬ IsOrbitalIntegral K v γ τ (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h

end OrbitalIntegral

section UnitFactor

variable (K : Type) [Field K] [NumberField K]


public theorem unitFinSet_eq :
    unitFinSet K = integralUnitsSet (AdelicLevel.integralFiniteAdeles (𝓞 K) K) := by
  ext h
  simp only [unitFinSet, Set.mem_ofPred_eq, mem_localIntegralSet, mem_integralUnitsSet,
    AdelicLevel.integralFiniteAdeles, ← map_inv, AdelicLevel.finComponent_apply]
  exact ⟨fun H => ⟨fun i j v => (H v).1 i j, fun i j v => (H v).2 i j⟩,
    fun H v => ⟨fun i j => H.1 i j v, fun i j => H.2 i j v⟩⟩


public theorem one_mem_unitFinSet : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∈ unitFinSet K :=
  fun v => by rw [map_one]; exact one_mem_localIntegralSet K v


public theorem isCompact_unitFinSet : IsCompact (unitFinSet K) := by
  rw [unitFinSet_eq]
  exact isCompact_integralUnitsSet (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)


public theorem isOpen_unitFinSet : IsOpen (unitFinSet K) := by
  rw [unitFinSet_eq]
  exact isOpen_integralUnitsSet (AdelicLevel.isOpen_integralFiniteAdeles (𝓞 K) K)


public theorem isFinTestFactor_indicator_unitFinSet :
    IsFinTestFactor K ((unitFinSet K).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_unitFinSet K) (isCompact_unitFinSet K).isClosed,
    HasCompactSupport.intro (isCompact_unitFinSet K) fun _ hg => by simp [hg]⟩

end UnitFactor

section Tier

variable (K : Type) [Field K] [NumberField K]


public theorem unitFinSet_eq_finiteIntegralGL2 :
    unitFinSet K = (AdelicLevel.finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  ext h
  rw [unitFinSet_eq, SetLike.mem_coe, AdelicLevel.mem_finiteIntegralGL2_iff]
  exact Iff.rfl


public theorem indicator_unitFinSet_mul_left {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (unitFinSet K).indicator (fun _ => (1 : ℂ)) (u * x) =
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) x := by
  have key : u * x ∈ unitFinSet K ↔ x ∈ unitFinSet K := by
    rw [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_left _ hu
  by_cases hx : x ∈ unitFinSet K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]


public theorem indicator_unitFinSet_mul_right {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (unitFinSet K).indicator (fun _ => (1 : ℂ)) (x * u) =
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) x := by
  have key : x * u ∈ unitFinSet K ↔ x ∈ unitFinSet K := by
    rw [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_right _ hu
  by_cases hx : x ∈ unitFinSet K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]


public theorem IsBiInvariantUnder.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsBiInvariantUnder K V f) :
    IsBiInvariantUnder K U f :=
  fun u hu => hf u (hUV hu)


public theorem isBiInvariantUnder_bot (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    IsBiInvariantUnder K ⊥ f := by
  intro u hu g
  rw [Subgroup.mem_bot.1 hu, one_mul, mul_one]
  exact ⟨rfl, rfl⟩


public theorem IsUnitFactorizableAt.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K V S f) : IsUnitFactorizableAt K U S f :=
  ⟨hf.1.mono K hUV, hf.2⟩


public theorem IsUnitFactorizableAt.isBiInvariantUnder {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K U S f) : IsBiInvariantUnder K U f :=
  hf.1


public theorem IsUnitFactorizableAt.isFactorizableTestFn {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K U S f) : IsFactorizableTestFn K f := by
  obtain ⟨-, fa, ff, _, hfa, hff, -, -, -, hf⟩ := hf
  exact ⟨fa, ff, hfa, hff, hf⟩


public theorem isIntegralLevel_bot : IsIntegralLevel K ⊥ := by
  intro u hu
  rw [Subgroup.mem_bot.1 hu, map_one, map_one]
  exact ⟨rfl, one_mem _⟩


public theorem isIntegralLevel_levelOne_inf_ker (N : Ideal (𝓞 K)) :
    IsIntegralLevel K (AdelicLevel.levelOne (𝓞 K) K N ⊓ (AdelicLevel.glArch (𝓞 K) K).ker) := by
  intro u hu
  obtain ⟨hlev, harch⟩ := Subgroup.mem_inf.1 hu
  refine ⟨MonoidHom.mem_ker.1 harch, ?_⟩
  have h0 := AdelicLevel.finiteLevelOne_le_finiteLevelZero (𝓞 K) K N (AdelicLevel.mem_levelOne_iff.1 hlev)
  exact AdelicLevel.mem_finiteIntegralGL2_iff.2 ⟨h0.1.integral, h0.2.integral⟩


public theorem isUnitFactorizableAt_mul_indicator_unitFinSet {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (hfa : IsArchTestFactor K fa) {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    (hU : IsIntegralLevel K U) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableAt K U S fun g => fa (AdelicLevel.glArch (𝓞 K) K g) *
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 K) K g) := by
  refine ⟨fun u hu g => ?_, fa, (unitFinSet K).indicator fun _ => (1 : ℂ),
    fun v => (localIntegralSet K v).indicator fun _ => (1 : ℂ), hfa,
    isFinTestFactor_indicator_unitFinSet K, fun v _ => isLocalTestFn_indicator_localIntegralSet K v,
    fun h hS => ?_, fun h hS => ?_, fun _ => rfl⟩
  · obtain ⟨hu1, hu2⟩ := hU u hu
    constructor
    · dsimp only
      rw [map_mul, map_mul, hu1, one_mul, indicator_unitFinSet_mul_left K hu2]
    · dsimp only
      rw [map_mul, map_mul, hu1, mul_one, indicator_unitFinSet_mul_right K hu2]
  · by_cases hall : h ∈ unitFinSet K
    · rw [Set.indicator_of_mem hall]
      exact (Finset.prod_eq_one fun v _ => Set.indicator_of_mem (hall v) _).symm
    · rw [Set.indicator_of_notMem hall]
      obtain ⟨v, hv⟩ : ∃ v, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v := by
        by_contra hcon
        exact hall fun v => by_contra fun hv => hcon ⟨v, hv⟩
      have hvS : v ∈ S := by
        by_contra hvS
        exact hv (hS v hvS)
      exact (Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _)).symm
  · obtain ⟨v, -, hv⟩ := hS
    have hnot : h ∉ unitFinSet K := fun hall => hv (hall v)
    exact Set.indicator_of_notMem hnot _


public theorem isUnitFactorizableAt_zero (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) : IsUnitFactorizableAt K U S fun _ => 0 := by
  refine ⟨fun _ _ _ => ⟨rfl, rfl⟩, ?_⟩
  simpa using
    (isUnitFactorizableAt_mul_indicator_unitFinSet K (isArchTestFactor_zero K) (isIntegralLevel_bot K) S).2

end Tier

section RegularSemisimple

variable {A : Type*} [CommRing A]


public theorem isRegularSemisimple_iff (g : GL (Fin 2) A) :
    IsRegularSemisimple g ↔
      IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A)) :=
  Iff.rfl


public theorem isRegularSemisimple_iff_ne_zero {F : Type*} [Field F] (g : GL (Fin 2) F) :
    IsRegularSemisimple g ↔
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) F) ≠ 0 :=
  isUnit_iff_ne_zero


public theorem IsRegularSemisimple.conj {g : GL (Fin 2) A} (hg : IsRegularSemisimple g) (x : GL (Fin 2) A) :
    IsRegularSemisimple (x⁻¹ * g * x) := by
  unfold IsRegularSemisimple at hg ⊢
  have htr : Matrix.trace ((x⁻¹ * g * x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  have hdet : Matrix.det ((x⁻¹ * g * x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.det (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  rw [htr, hdet]
  exact hg

end RegularSemisimple

end AutomorphicForm

end
-- updated on 2026-11-16

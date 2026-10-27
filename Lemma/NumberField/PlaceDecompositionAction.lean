import Mathlib
import Abbrev.NumberField_PlaceDecompositionAction

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped Pointwise

namespace NumberField.PlaceDecomp

section general
variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem uniformContinuous_congr_of_forall_eq (v : Valuation K Γ₀) (f : K ≃+* K) (h : ∀ x, v (f x) = v x) :
    UniformContinuous (WithVal.congr v v f) := by
  apply uniformContinuous_addMonoidHom_of_continuous
  apply continuous_of_continuousAt_zero (WithVal.congr v v f).toAddMonoidHom
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  refine ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have key : Valued.v ((WithVal.congr v v f).toAddMonoidHom x) = Valued.v x := by
    change Valued.v (WithVal.congr _ _ _ x) = _
    rw [WithVal.congr_apply, WithVal.valued_toVal, ← WithVal.apply_ofVal]
    exact h _
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [key]

theorem le_exp_neg_one_of_lt_one {t : WithZero (Multiplicative ℤ)} (ht : t < 1) : t ≤ WithZero.exp (-1) := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact zero_le
  · rw [← WithZero.exp_log h0] at ht ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ht
    rw [WithZero.exp_le_exp]
    omega

theorem apply_eq_of_isEquiv_comap (v : Valuation K (WithZero (Multiplicative ℤ))) (f : K ≃+* K)
    (hf : v.IsEquiv (v.comap (f : K →+* K))) (hπ : ∃ π : K, v π = WithZero.exp (-1)) (x : K) : v (f x) = v x := by

  have hle : ∀ a b : K, v a ≤ v b ↔ v (f a) ≤ v (f b) := fun a b => hf a b

  have step1 : ∀ (g : K ≃+* K), (∀ a b : K, v a ≤ v b ↔ v (g a) ≤ v (g b)) → ∀ π : K, v π = WithZero.exp (-1) →
      v (g π) = WithZero.exp (-1) := by
    intro g hg π hπ
    have hπ1 : v π < 1 := by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    apply le_antisymm
    · apply le_exp_neg_one_of_lt_one
      have : ¬ v (g 1) ≤ v (g π) := fun h => (not_le.2 hπ1) (by simpa using (hg 1 π).2 h)
      simpa using not_le.1 this
    ·
      have hy : v (g (g.symm π)) = WithZero.exp (-1) := by rw [g.apply_symm_apply, hπ]
      have hy1 : v (g.symm π) < 1 := by
        have : ¬ v (g 1) ≤ v (g (g.symm π)) := by
          rw [map_one, map_one, hy, not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
        have : ¬ v 1 ≤ v (g.symm π) := fun h => this ((hg _ _).1 h)
        simpa using not_le.1 this
      have := (hg (g.symm π) π).1 ((le_exp_neg_one_of_lt_one hy1).trans hπ.ge)
      rwa [hy] at this
  obtain ⟨π, hvπ⟩ := hπ
  have hfπ : v (f π) = WithZero.exp (-1) := step1 f hle π hvπ

  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · set m : ℤ := WithZero.log (v x) with hm
    have hvx : v x = WithZero.exp m := (WithZero.exp_log ((map_ne_zero v).2 hx)).symm
    have hz : v (π ^ (-m)) = WithZero.exp m := by
      rw [map_zpow₀, hvπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    have hfz : v (f (π ^ (-m))) = WithZero.exp m := by
      rw [map_zpow₀, map_zpow₀, hfπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    have h1 : v (f x) ≤ v (f (π ^ (-m))) := (hle _ _).1 (by rw [hvx, hz])
    have h2 : v (f (π ^ (-m))) ≤ v (f x) := (hle _ _).1 (by rw [hvx, hz])
    rw [hvx]
    exact le_antisymm (h1.trans hfz.le) (hfz.ge.trans h2)

end general

variable {E K : Type*} [Field E] [Field K] [NumberField K] [Algebra E K] {w : HeightOneSpectrum (𝓞 K)}

theorem isEquiv_comap_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    (w.valuation K).IsEquiv ((w.valuation K).comap (σ : K →+* K)) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [MulAction.mem_stabilizer_iff] at hσ
  have : σ • x ∈ σ • (w.valuation K).valuationSubring ↔ x ∈ (w.valuation K).valuationSubring :=
    ValuationSubring.smul_mem_pointwise_smul_iff
  rw [hσ, Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff] at this
  rw [Valuation.comap_apply]
  exact this.symm

theorem valuation_apply_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) (x : K) :
    w.valuation K (σ x) = w.valuation K x :=
  apply_eq_of_isEquiv_comap (w.valuation K) (σ : K ≃+* K) (isEquiv_comap_of_mem σ hσ) (w.valuation_exists_uniformizer K) x

theorem uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    UniformContinuous (WithVal.congr (w.valuation K) (w.valuation K) (σ : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq (w.valuation K) (σ : K ≃+* K) (valuation_apply_of_mem σ hσ)

noncomputable def actRingEquiv (σ : decomp E K w) : w.adicCompletion K ≃+* w.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2).continuous
      (by
        rw [WithVal.congr_symm]
        exact (uniformContinuous_congr_of_mem ((σ⁻¹ : decomp E K w) : K ≃ₐ[E] K) (σ⁻¹).2).continuous))).trans
    (HeightOneSpectrum.adicCompletion.equiv K w).symm

theorem actRingEquiv_apply (σ : decomp E K w) (x : w.adicCompletion K) :
    (actRingEquiv σ x).toCompletion
      = UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion :=
  rfl

theorem actRingEquiv_coe (σ : decomp E K w) (x : WithVal (w.valuation K)) :
    actRingEquiv σ (x : w.adicCompletion K)
      = ((WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K) x : WithVal (w.valuation K)) : w.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]

theorem continuous_actRingEquiv (σ : decomp E K w) : Continuous (actRingEquiv σ) := by
  have : (actRingEquiv σ : w.adicCompletion K → w.adicCompletion K)
      = HeightOneSpectrum.adicCompletion.ofCompletion ∘
        UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        HeightOneSpectrum.adicCompletion.toCompletion :=
    funext fun x => HeightOneSpectrum.adicCompletion.ext (h := actRingEquiv_apply σ x)
  rw [this]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).comp
    (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

theorem actRingEquiv_one : actRingEquiv (1 : decomp E K w) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  apply HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply]
  change _ = id x.toCompletion
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map continuous_id fun a => ?_) _
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem ((1 : decomp E K w) : K ≃ₐ[E] K) (1 : decomp E K w).2)]
  rfl

theorem actRingEquiv_mul (σ τ : decomp E K w) : actRingEquiv (σ * τ) = (actRingEquiv τ).trans (actRingEquiv σ) := by
  apply RingEquiv.ext
  intro x
  apply HeightOneSpectrum.adicCompletion.ext
  change (actRingEquiv (σ * τ) x).toCompletion = (actRingEquiv σ (actRingEquiv τ x)).toCompletion
  rw [actRingEquiv_apply, actRingEquiv_apply, actRingEquiv_apply]
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map
    (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map) fun a => ?_) _
  change _ = UniformSpace.Completion.map _ (UniformSpace.Completion.map _ _)
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem ((σ * τ : decomp E K w) : K ≃ₐ[E] K) (σ * τ).2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (τ : K ≃ₐ[E] K) τ.2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]
  rfl

noncomputable def actHom : decomp E K w →* (w.adicCompletion K ≃+* w.adicCompletion K) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

noncomputable scoped instance instSMulWithVal : SMul (decomp E K w) (WithVal (w.valuation K)) where
  smul σ y := WithVal.toVal (w.valuation K) ((σ : K ≃ₐ[E] K) y.ofVal)

noncomputable scoped instance instMulActionWithVal : MulAction (decomp E K w) (WithVal (w.valuation K)) where
  one_smul y := by
    change WithVal.toVal _ (((1 : decomp E K w) : K ≃ₐ[E] K) y.ofVal) = y
    rw [Subgroup.coe_one, AlgEquiv.one_apply, WithVal.toVal_ofVal]
  mul_smul σ τ y := by
    change WithVal.toVal _ (((σ * τ : decomp E K w) : K ≃ₐ[E] K) y.ofVal) =
      WithVal.toVal _ ((σ : K ≃ₐ[E] K)
        (WithVal.ofVal (WithVal.toVal _ (((τ : decomp E K w) : K ≃ₐ[E] K) y.ofVal))))
    rw [Subgroup.coe_mul, AlgEquiv.mul_apply, WithVal.ofVal_toVal]

noncomputable scoped instance instDistribMulActionWithVal : DistribMulAction (decomp E K w) (WithVal (w.valuation K)) where
  smul_zero σ := by
    change WithVal.toVal _ ((σ : K ≃ₐ[E] K) (0 : WithVal (w.valuation K)).ofVal) = 0
    rw [WithVal.ofVal_zero, map_zero, WithVal.toVal_zero]
  smul_add σ x y := by
    change WithVal.toVal _ ((σ : K ≃ₐ[E] K) (x + y).ofVal) =
      WithVal.toVal _ ((σ : K ≃ₐ[E] K) x.ofVal) + WithVal.toVal _ ((σ : K ≃ₐ[E] K) y.ofVal)
    rw [WithVal.ofVal_add, map_add, WithVal.toVal_add]

noncomputable scoped instance instUniformContinuousConstSMul :
    UniformContinuousConstSMul (decomp E K w) (WithVal (w.valuation K)) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

noncomputable scoped instance instMulSemiringAction : MulSemiringAction (decomp E K w) (w.adicCompletion K) where
  smul σ x := actRingEquiv σ x
  one_smul x := by change actRingEquiv 1 x = x; rw [actRingEquiv_one]; rfl
  mul_smul σ τ x := by change actRingEquiv (σ * τ) x = actRingEquiv σ (actRingEquiv τ x); rw [actRingEquiv_mul]; rfl
  smul_zero σ := by change actRingEquiv σ 0 = 0; rw [map_zero]
  smul_add σ x y := by change actRingEquiv σ (x + y) = actRingEquiv σ x + actRingEquiv σ y; rw [map_add]
  smul_one σ := by change actRingEquiv σ 1 = 1; rw [map_one]
  smul_mul σ x y := by change actRingEquiv σ (x * y) = actRingEquiv σ x * actRingEquiv σ y; rw [map_mul]

noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K w) (w.adicCompletion K)ˣ :=
  Units.mulDistribMulActionRight

theorem smul_withVal_def (σ : decomp E K w) (y : WithVal (w.valuation K)) :
    σ • y = WithVal.toVal (w.valuation K) ((σ : K ≃ₐ[E] K) y.ofVal) := rfl

theorem smul_def (σ : decomp E K w) (x : w.adicCompletion K) : σ • x = actRingEquiv σ x := rfl

set_option synthInstance.maxHeartbeats 200000 in
theorem coe_smul_units (σ : decomp E K w) (u : (w.adicCompletion K)ˣ) : ((σ • u : (w.adicCompletion K)ˣ) : w.adicCompletion K) = σ • (u : w.adicCompletion K) := rfl

section integers

open WithZeroTopology in

theorem valued_actRingEquiv (σ : decomp E K w) (x : w.adicCompletion K) : Valued.v (actRingEquiv σ x) = Valued.v x := by
  have hclosed : IsClosed {y : w.adicCompletion K | Valued.v (actRingEquiv σ y) = Valued.v y} := by
    have : {y : w.adicCompletion K | Valued.v (actRingEquiv σ y) = Valued.v y}
        = {y | Valued.v.restrict (actRingEquiv σ y) = Valued.v.restrict y} :=
      Set.ext fun y => (Valuation.restrict_inj _).symm
    rw [this]
    exact isClosed_eq (Valued.continuous_valuation.comp (continuous_actRingEquiv σ)) Valued.continuous_valuation
  obtain ⟨x, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w x
  refine UniformSpace.Completion.induction_on
    (p := fun y => Valued.v (actRingEquiv σ (.ofCompletion y)) = Valued.v (HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K)) x
    (by simpa only [Set.preimage_ofPred_eq] using hclosed.preimage (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)) fun a => ?_
  show Valued.v (actRingEquiv σ (a : w.adicCompletion K)) = Valued.v (a : w.adicCompletion K)
  rw [actRingEquiv_coe, HeightOneSpectrum.adicCompletion.valued_ofCompletion, HeightOneSpectrum.adicCompletion.valued_ofCompletion,
    Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, ← WithVal.apply_ofVal, ← WithVal.apply_ofVal,
    WithVal.congr_apply]
  exact valuation_apply_of_mem (σ : K ≃ₐ[E] K) σ.2 a.ofVal

theorem valued_smul (σ : decomp E K w) (x : w.adicCompletion K) : Valued.v (σ • x) = Valued.v x :=
  valued_actRingEquiv σ x

theorem smul_mem_adicCompletionIntegers_iff (σ : decomp E K w) (x : w.adicCompletion K) :
    σ • x ∈ w.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, valued_smul]

noncomputable scoped instance instSMulIntegers : SMul (decomp E K w) (w.adicCompletionIntegers K) :=
  ⟨fun σ x => ⟨σ • (x : w.adicCompletion K), (smul_mem_adicCompletionIntegers_iff σ _).2 x.2⟩⟩

theorem coe_smul_integers (σ : decomp E K w) (x : w.adicCompletionIntegers K) :
    ((σ • x : w.adicCompletionIntegers K) : w.adicCompletion K) = σ • (x : w.adicCompletion K) := rfl

end integers

end NumberField.PlaceDecomp

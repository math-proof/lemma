import Mathlib

set_option autoImplicit false

noncomputable section

open MonoidWithZeroHom WithZeroTopology UniformSpace

namespace ValuationSubring

variable {K : Type*} [Field K] (A : ValuationSubring K) (F : Type*) [Field F] [Algebra F K]

def DecompositionIsometric : Prop :=
  ∀ (σ : A.decompositionSubgroup F) (x : K),
    A.valuation ((σ : K ≃ₐ[F] K) x) = A.valuation x

variable {A F}

instance charZero_completion [CharZero K] : CharZero A.valuation.Completion :=
  charZero_of_injective_ringHom
    (UniformSpace.Completion.coeRingHom (α := WithVal A.valuation)).injective

theorem smul_withVal_def (σ : A.decompositionSubgroup F) (x : WithVal A.valuation) :
    σ • x = WithVal.toVal A.valuation ((σ : K ≃ₐ[F] K) x.ofVal) := rfl

instance mulSemiringActionWithVal :
    MulSemiringAction (A.decompositionSubgroup F) (WithVal A.valuation) where
  one_smul x := by rw [smul_withVal_def]; rfl
  mul_smul σ τ x := by simp only [smul_withVal_def]; rfl
  smul_zero σ := by rw [smul_withVal_def, WithVal.ofVal_zero, map_zero]; rfl
  smul_add σ x y := by simp only [smul_withVal_def, WithVal.ofVal_add, map_add]; rfl
  smul_one σ := by rw [smul_withVal_def, WithVal.ofVal_one, map_one]; rfl
  smul_mul σ x y := by simp only [smul_withVal_def, WithVal.ofVal_mul, map_mul]; rfl

theorem valued_smul_withVal (h : A.DecompositionIsometric F) (σ : A.decompositionSubgroup F)
    (x : WithVal A.valuation) : Valued.v (σ • x) = Valued.v x := by
  rw [smul_withVal_def]
  change A.valuation ((σ : K ≃ₐ[F] K) x.ofVal) = A.valuation x.ofVal
  exact h σ _

theorem continuous_smul_withVal (h : A.DecompositionIsometric F) (σ : A.decompositionSubgroup F) :
    Continuous (fun x : WithVal A.valuation => σ • x) := by
  let f : WithVal A.valuation →+* WithVal A.valuation :=
    MulSemiringAction.toRingHom (A.decompositionSubgroup F) (WithVal A.valuation) σ
  change Continuous f
  apply continuous_of_continuousAt_zero f
  rw [ContinuousAt, map_zero]
  refine ((Valued.hasBasis_nhds_zero (WithVal A.valuation) A.ValueGroup).tendsto_iff
    (Valued.hasBasis_nhds_zero (WithVal A.valuation) A.ValueGroup)).mpr
    fun γ _ => ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  have hres : Valued.v.restrict (f x) = Valued.v.restrict x :=
    (Valuation.restrict_inj _).mpr (valued_smul_withVal h σ x)
  rw [hres]
  exact hx

instance uniformContinuousConstSMul_withVal [h : Fact (A.DecompositionIsometric F)] :
    UniformContinuousConstSMul (A.decompositionSubgroup F) (WithVal A.valuation) :=
  ⟨fun σ => uniformContinuous_addMonoidHom_of_continuous
    (f := (MulSemiringAction.toRingHom (A.decompositionSubgroup F) (WithVal A.valuation) σ :
      WithVal A.valuation →+ WithVal A.valuation)) (continuous_smul_withVal h.out σ)⟩

section Completion

variable [h : Fact (A.DecompositionIsometric F)]

theorem smul_completion_coe (σ : A.decompositionSubgroup F) (a : K) :
    σ • ((a : K) : A.valuation.Completion) =
      (((σ : K ≃ₐ[F] K) a : K) : A.valuation.Completion) :=
  (Completion.coe_smul σ (WithVal.toVal A.valuation a)).symm

omit h in

theorem continuous_smul_completion (σ : A.decompositionSubgroup F) :
    Continuous (fun x : A.valuation.Completion => σ • x) :=
  continuous_const_smul σ

instance mulSemiringActionCompletion :
    MulSemiringAction (A.decompositionSubgroup F) A.valuation.Completion :=
  { (inferInstance : DistribMulAction (A.decompositionSubgroup F) A.valuation.Completion) with
    smul_one := fun σ => by
      rw [← Completion.coe_one, ← Completion.coe_smul, smul_one]
    smul_mul := fun σ x y =>
      Completion.induction_on₂ x y
        (isClosed_eq ((continuous_fst.fun_mul continuous_snd).fun_const_smul (σ : A.decompositionSubgroup F))
          ((continuous_fst.fun_const_smul (σ : A.decompositionSubgroup F)).fun_mul
            (continuous_snd.fun_const_smul (σ : A.decompositionSubgroup F))))
        fun a b => by simp only [← Completion.coe_mul, ← Completion.coe_smul, smul_mul'] }

theorem valuation_smul_completion (σ : A.decompositionSubgroup F) (x : A.valuation.Completion) :
    Valued.v (σ • x) = Valued.v x := by
  rw [← Valuation.restrict_inj]
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((Valued.continuous_valuation (K := A.valuation.Completion)).comp
      (continuous_smul_completion σ)) (Valued.continuous_valuation (K := A.valuation.Completion))
  | ih a =>
    rw [Valuation.restrict_inj, ← Completion.coe_smul, Valued.valuedCompletion_apply,
      Valued.valuedCompletion_apply]
    exact valued_smul_withVal h.out σ a

theorem eq_smul_completion_of_continuous (σ : A.decompositionSubgroup F)
    (g : A.valuation.Completion →+* A.valuation.Completion) (hg : Continuous g)
    (hext : ∀ a : K, g ((a : K) : A.valuation.Completion) =
      (((σ : K ≃ₐ[F] K) a : K) : A.valuation.Completion)) (x : A.valuation.Completion) :
    g x = σ • x := by
  refine congrFun (Completion.ext hg (continuous_smul_completion σ) fun a => ?_) x
  refine (hext (WithVal.equiv A.valuation a)).trans ?_
  exact (smul_completion_coe σ _).symm

def completionRingAut :
    A.decompositionSubgroup F →* (A.valuation.Completion ≃+* A.valuation.Completion) :=
  MulSemiringAction.toRingAut (A.decompositionSubgroup F) A.valuation.Completion

theorem completionRingAut_apply (σ : A.decompositionSubgroup F) (x : A.valuation.Completion) :
    completionRingAut σ x = σ • x := by
  simp only [completionRingAut, MulSemiringAction.toRingAut_apply,
    MulSemiringAction.toRingEquiv_apply_apply]

end Completion

end ValuationSubring

end

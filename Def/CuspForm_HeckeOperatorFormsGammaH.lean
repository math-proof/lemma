module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Def.CohCarrier_Inst
public import Theorem.ModularForm.HeckeOperator

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup

namespace CuspForm

section GammaH

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

def gammaLift (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : Gamma0 M :=
  Classical.choose (CohCarrier.gamma0Units_surjective M d)

def unitOfPrimeNotDvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : (ZMod M)ˣ :=
  ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)

def StableD (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) : Prop :=
  ∀ (σ : Gamma0 M) (f : CuspForm (CohCarrier.GammaH M H) k) (c : OnePoint ℝ),
    IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
      OnePoint.IsZeroAt c (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) k

def StableU (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (q : ℕ) : Prop :=
  ∀ f : CuspForm (CohCarrier.GammaH M H) k,
    (∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)),
      (ModularForm.heckeU k q ⇑f) ∣[k] γ = ModularForm.heckeU k q ⇑f) ∧
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k q ⇑f) ∧
    ∀ c : OnePoint ℝ, IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
      OnePoint.IsZeroAt c (ModularForm.heckeU k q ⇑f) k

def StableT (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ℓ : ℕ) : Prop :=
  ∀ (ρ : Gamma0 M), (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ →
    ∀ f : CuspForm (CohCarrier.GammaH M H) k,
      (∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)),
        (ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))) ∣[k] γ =
        ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))) ∧
      MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))) ∧
      ∀ c : OnePoint ℝ, IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) →
        OnePoint.IsZeroAt c
          (ModularForm.heckeU k ℓ ⇑f +
            (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
              ModularForm.heckeDiagMatrix ℓ))) k

def diamondLinHOf (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k where
  toFun f :=
    { toFun := ⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ))
      slash_action_eq' := fun γ hγ => by
        obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
        rw [← SlashAction.slash_mul, ← map_mul,
          show (gammaLift M d : SL(2, ℤ)) * g = ((gammaLift M d : SL(2, ℤ)) * g * (gammaLift M d : SL(2, ℤ))⁻¹) *
            (gammaLift M d : SL(2, ℤ)) by rw [inv_mul_cancel_right],
          map_mul, SlashAction.slash_mul,
          SlashInvariantFormClass.slash_action_eq f _
            (Subgroup.mem_map_of_mem _ (CohCarrier.conj_mem_GammaH M H (gammaLift M d) ⟨g, hg⟩))]
      holo' := (CuspFormClass.holo f).slash k _
      zero_at_cusps' := fun hc => hD (gammaLift M d) f _ hc }
  map_add' f g := DFunLike.coe_injective <| by
    show (⇑(f + g)) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ))) +
      (⇑g ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)))
    rw [CuspForm.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    show (⇑(c • f)) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      c • (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)))
    rw [CuspForm.IsGLPos.coe_smul]
    exact ModularForm.SL_smul_slash k (gammaLift M d : SL(2, ℤ)) ⇑f c

open Classical in

def diamondLinH (k : ℤ) (d : (ZMod M)ˣ) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k :=
  if hD : StableD M H k then diamondLinHOf k hD d else 0

def heckeULinHOf (k : ℤ) {q : ℕ} (hU : StableU M H k q) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k where
  toFun f :=
    { toFun := ModularForm.heckeU k q ⇑f
      slash_action_eq' := fun γ hγ => (hU f).1 γ hγ
      holo' := (hU f).2.1
      zero_at_cusps' := fun hc => (hU f).2.2 _ hc }
  map_add' f g := DFunLike.coe_injective <|
    show ModularForm.heckeU k q ⇑(f + g) = ModularForm.heckeU k q ⇑f + ModularForm.heckeU k q ⇑g by
      rw [CuspForm.coe_add, ModularForm.heckeU_add]
  map_smul' c f := DFunLike.coe_injective <|
    show ModularForm.heckeU k q ⇑(c • f) = c • ModularForm.heckeU k q ⇑f by
      rw [CuspForm.IsGLPos.coe_smul, ModularForm.heckeU_smul]

open Classical in

def heckeULinH (k : ℤ) (q : ℕ) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k :=
  if hU : StableU M H k q then heckeULinHOf k hU else 0

def heckeTLinHOf (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hT : StableT M H k ℓ) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k :=
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  { toFun := fun f =>
      { toFun := ModularForm.heckeU k ℓ ⇑f +
          (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
            (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
              ModularForm.heckeDiagMatrix ℓ))
        slash_action_eq' := fun γ hγ => (hT _ (gammaLift_apply_11 hℓ hℓM) f).1 γ hγ
        holo' := (hT _ (gammaLift_apply_11 hℓ hℓM) f).2.1
        zero_at_cusps' := fun hc => (hT _ (gammaLift_apply_11 hℓ hℓM) f).2.2 _ hc }
    map_add' := fun f g => DFunLike.coe_injective <| by
      show ModularForm.heckeU k ℓ ⇑(f + g) + (⇑(f + g)) ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) =
        (ModularForm.heckeU k ℓ ⇑f + ⇑f ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ)) +
        (ModularForm.heckeU k ℓ ⇑g + ⇑g ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))
      rw [CuspForm.coe_add, ModularForm.heckeU_add, SlashAction.add_slash]
      abel
    map_smul' := fun c f => DFunLike.coe_injective <| by
      show ModularForm.heckeU k ℓ ⇑(c • f) + (⇑(c • f)) ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) =
        c • (ModularForm.heckeU k ℓ ⇑f + ⇑f ∣[k]
          ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ))
      rw [CuspForm.IsGLPos.coe_smul, ModularForm.heckeU_smul, SlashAction.slash_mul, SlashAction.slash_mul, smul_add]
      congr 1
      rw [show (c • ⇑f) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        c • (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
          (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ))) from
        ModularForm.SL_smul_slash k _ ⇑f c]
      simp only [ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix, ContinuousAlgEquiv.refl_apply] }

open Classical in

def heckeTLinH (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] CuspForm (CohCarrier.GammaH M H) k :=
  if hT : StableT M H k ℓ then heckeTLinHOf k hℓ hℓM hT else 0

end GammaH

end CuspForm

end

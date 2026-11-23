module

public import Mathlib.NumberTheory.ModularForms.Basic
public import Theorem.ZMod.Inst
public import Theorem.ModularForm.HeckeOperator

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open CongruenceSubgroup

namespace CuspForm

section GammaH

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

public theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H


public theorem gamma0Units_gammaLift (d : (ZMod M)ˣ) : CohCarrier.gamma0Units M (gammaLift M d) = d :=
  Classical.choose_spec (CohCarrier.gamma0Units_surjective M d)


public theorem gammaLift_apply_11 {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ((((gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ := by
  have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) (gamma0Units_gammaLift (unitOfPrimeNotDvd hℓ hℓM))
  simp [unitOfPrimeNotDvd, CohCarrier.val_gamma0Units] at this
  exact this


public theorem mul_inv_mem_GammaH_of_gamma0Units_eq (ρ σ : Gamma0 M)
    (h : CohCarrier.gamma0Units M ρ = CohCarrier.gamma0Units M σ) :
    (ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨(ρ * σ⁻¹).2, ?_⟩
  have e1 : (⟨(ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹, (ρ * σ⁻¹).2⟩ : Gamma0 M) = ρ * σ⁻¹ := rfl
  rw [e1, map_mul, map_inv, h, mul_inv_cancel]
  exact one_mem H


public theorem slash_mapGL_eq_of_gamma0Units_eq (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (ρ σ : Gamma0 M) (h : CohCarrier.gamma0Units M ρ = CohCarrier.gamma0Units M σ) (A : GL (Fin 2) ℝ) :
    f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) := by
  have e : ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [e, mul_assoc, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map_of_mem _ (mul_inv_mem_GammaH_of_gamma0Units_eq ρ σ h))]


public theorem diamondLinH_eq (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ) :
    (diamondLinH k d : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] _) = diamondLinHOf k hD d := by
  rw [diamondLinH, dif_pos hD]


public theorem coe_diamondLinH_apply (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ)
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    ⇑(diamondLinH k d f) =
      ⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  rw [diamondLinH_eq k hD]; rfl


public theorem coe_diamondLinH_eq_slash (k : ℤ) (hD : StableD M H k) (d : (ZMod M)ˣ) (σ : Gamma0 M)
    (hσ : CohCarrier.gamma0Units M σ = d) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ⇑(diamondLinH k d f) = ⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  rw [coe_diamondLinH_apply k hD]
  have := slash_mapGL_eq_of_gamma0Units_eq (H := H) k
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) (gammaLift M d) σ
    ((gamma0Units_gammaLift d).trans hσ.symm) 1
  rwa [mul_one, mul_one] at this


public theorem heckeULinH_eq (k : ℤ) {q : ℕ} (hU : StableU M H k q) :
    (heckeULinH k q : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] _) = heckeULinHOf k hU := by
  rw [heckeULinH, dif_pos hU]


public theorem coe_heckeULinH_apply (k : ℤ) {q : ℕ} (hU : StableU M H k q)
    (f : CuspForm (CohCarrier.GammaH M H) k) : ⇑(heckeULinH k q f) = ModularForm.heckeU k q ⇑f := by
  rw [heckeULinH_eq k hU]; rfl


public theorem heckeTLinH_eq (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hT : StableT M H k ℓ) :
    (heckeTLinH k hℓ hℓM : CuspForm (CohCarrier.GammaH M H) k →ₗ[ℂ] _) = heckeTLinHOf k hℓ hℓM hT := by
  rw [heckeTLinH, dif_pos hT]


public theorem coe_heckeTLinH_apply (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hT : StableT M H k ℓ)
    (f : CuspForm (CohCarrier.GammaH M H) k) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ⇑(heckeTLinH k hℓ hℓM f) = ModularForm.heckeU k ℓ ⇑f +
      (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ
        (gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
          ModularForm.heckeDiagMatrix ℓ)) := by
  rw [heckeTLinH_eq k hℓ hℓM hT]; rfl


public theorem coe_heckeTLinH_eq (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hT : StableT M H k ℓ) (ρ : Gamma0 M)
    (hρ : (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ⇑(heckeTLinH k hℓ hℓM f) = ModularForm.heckeU k ℓ ⇑f +
      (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
        ModularForm.heckeDiagMatrix ℓ)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [coe_heckeTLinH_apply k hℓ hℓM hT]
  congr 1
  refine slash_mapGL_eq_of_gamma0Units_eq (H := H) k
    (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) _ ρ ?_ _
  ext
  rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
  show ((((gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) =
    ((((ρ : SL(2, ℤ)) 1 1 : ℤ)) : ZMod M)
  rw [gammaLift_apply_11, hρ]

end GammaH

end CuspForm

end

module

public import Mathlib
public import Theorem.Matrix.EulerFactor
public import Theorem.Ideal.Valuation.LowerRamificationGroup
public import Instance.ArtinL_Conductor
public import Notation.ArtinL_Conductor

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups Pointwise

namespace ArtinL

variable {n : ℕ}

open scoped ArtinL_Conductor


public theorem apply_mem_splittingField (ρ : Γℚ →* GL (Fin n) ℂ) (σ : Γℚ) {x : ℚbar}
    (hx : x ∈ splittingField ρ) : σ x ∈ splittingField ρ := by
  rintro ⟨τ, hτ⟩
  change τ (σ x) = σ x
  have hmem : σ⁻¹ * τ * σ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker] at hτ ⊢
    rw [map_mul, map_mul, hτ, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have h := hx ⟨σ⁻¹ * τ * σ, hmem⟩
  change (σ⁻¹ * τ * σ) x = x at h
  simpa [AlgEquiv.mul_apply] using congrArg σ h


@[simp] public theorem coe_smul_splittingField (ρ : Γℚ →* GL (Fin n) ℂ) (σ : Γℚ)
    (x : splittingField ρ) : ((σ • x : splittingField ρ) : ℚbar) = σ (x : ℚbar) := rfl


public theorem mem_placeUnder_iff (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (x : splittingField ρ) : x ∈ placeUnder ρ A ↔ (x : ℚbar) ∈ A := Iff.rfl


public theorem smul_mem_placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (σ : A.decompositionSubgroup ℚ) {x : splittingField ρ} (hx : x ∈ placeUnder ρ A) :
    (σ : Γℚ) • x ∈ placeUnder ρ A := by
  rw [mem_placeUnder_iff] at hx ⊢
  have h : (σ : Γℚ) • (x : ℚbar) ∈ (σ : Γℚ) • (A : ValuationSubring ℚbar) :=
    Set.smul_mem_smul_set hx
  rw [σ.2] at h
  exact h


@[simp] public theorem coe_coe_smul_placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (σ : A.decompositionSubgroup ℚ) (x : placeUnder ρ A) :
    (((σ • x : placeUnder ρ A) : splittingField ρ) : ℚbar) = (σ : Γℚ) ((x : splittingField ρ) : ℚbar) := rfl


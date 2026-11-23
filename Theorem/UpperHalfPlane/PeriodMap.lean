module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Algebra.Module.Hom

public section

namespace ModularCurve.Period

open UpperHalfPlane

open scoped MatrixGroups

variable (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ)


public theorem sub_eq_period (hF : IsEquivariantPrimitive Γ F) (γ : Γ) (z : ℍ) :
    F ((γ : SL(2, ℤ)) • z) - F z = hF.period γ := by
  obtain ⟨c, hc⟩ := hF γ
  rw [hc z, period, hc UpperHalfPlane.I]


@[simp]
public theorem period_one (hF : IsEquivariantPrimitive Γ F) : hF.period 1 = 0 := by
  have h := hF.sub_eq_period 1 UpperHalfPlane.I
  simpa using h.symm


public theorem period_mul (hF : IsEquivariantPrimitive Γ F) (γ δ : Γ) :
    hF.period (γ * δ) = hF.period γ + hF.period δ := by
  have h1 := hF.sub_eq_period (γ * δ) UpperHalfPlane.I
  have h2 := hF.sub_eq_period γ ((δ : SL(2, ℤ)) • UpperHalfPlane.I)
  have h3 := hF.sub_eq_period δ UpperHalfPlane.I
  have hsmul : ((γ * δ : Γ) : SL(2, ℤ)) • UpperHalfPlane.I
      = (γ : SL(2, ℤ)) • ((δ : SL(2, ℤ)) • UpperHalfPlane.I) := by
    rw [← mul_smul]; rfl
  rw [hsmul] at h1
  linear_combination h2 + h3 - h1


@[simp]
public theorem periodHom_apply (hF : IsEquivariantPrimitive Γ F) (γ : Γ) :
    hF.periodHom (Additive.ofMul γ) = hF.period γ :=
  rfl

end IsEquivariantPrimitive

section ParabolicHoms

variable (R : Type*) [Semiring R] (Γ : Subgroup SL(2, ℤ)) (A : Type*) [AddCommGroup A] [Module R A]


public theorem mem_parabolicHoms_iff {φ : Additive Γ →+ A} : φ ∈ parabolicHoms R Γ A ↔ IsParabolicHom Γ φ :=
  Iff.rfl

end ParabolicHoms

end ModularCurve.Period

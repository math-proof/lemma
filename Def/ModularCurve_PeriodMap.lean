module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Algebra.Module.Hom

@[expose] public section

namespace ModularCurve.Period

open UpperHalfPlane

open scoped MatrixGroups

variable (Γ : Subgroup SL(2, ℤ)) (F : ℍ → ℂ)

def IsEquivariantPrimitive : Prop :=
  ∀ γ : Γ, ∃ c : ℂ, ∀ z : ℍ, F ((γ : SL(2, ℤ)) • z) - F z = c

def IsParabolicHom {A : Type*} [AddCommGroup A] (φ : Additive Γ →+ A) : Prop :=
  ∀ γ : Γ, ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace ^ 2 = 4 → φ (Additive.ofMul γ) = 0

variable {Γ F}

namespace IsEquivariantPrimitive

noncomputable def period (_hF : IsEquivariantPrimitive Γ F) (γ : Γ) : ℂ :=
  F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I

noncomputable def periodHom (hF : IsEquivariantPrimitive Γ F) : Additive Γ →+ ℂ where
  toFun γ := hF.period (Additive.toMul γ)
  map_zero' := hF.period_one
  map_add' γ δ := hF.period_mul (Additive.toMul γ) (Additive.toMul δ)

end IsEquivariantPrimitive

section ParabolicHoms

variable (R : Type*) [Semiring R] (Γ : Subgroup SL(2, ℤ)) (A : Type*) [AddCommGroup A] [Module R A]

def parabolicHoms : Submodule R (Additive Γ →+ A) where
  carrier := {φ | IsParabolicHom Γ φ}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro φ ψ hφ hψ γ hγ
    show φ (Additive.ofMul γ) + ψ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, hψ γ hγ, add_zero]
  smul_mem' := by
    intro c φ hφ γ hγ
    show c • φ (Additive.ofMul γ) = 0
    rw [hφ γ hγ, smul_zero]

variable {R Γ A}

end ParabolicHoms

end ModularCurve.Period

end

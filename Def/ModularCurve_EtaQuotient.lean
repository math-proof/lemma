import Lemma.ModularCurve.ModularUnit
import Def.ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Discriminant

set_option autoImplicit false

noncomputable section

open scoped ModularForm MatrixGroups

namespace ModularCurve

def sharpIndex (ℓ : ℕ) : ℕ := Nat.gcd (ℓ - 1) 12

def sharpExp (ℓ : ℕ) : ℕ := 24 / sharpIndex ℓ


def etaProdPow (ℓ : ℕ) : PowerSeries ℚ := (etaProd ^ sharpExp ℓ).map (Int.castRingHom ℚ)


variable (ℓ : ℕ)

def sharpUnitFun (τ : UpperHalfPlane) : ℂ :=
  (η (τ : ℂ) / η ((ModularForm.heckeDiagMatrix ℓ • τ : UpperHalfPlane) : ℂ)) ^ sharpExp ℓ


section Series

variable [NeZero ℓ]

def sharpUnitSeries : LaurentSeries ℚ :=
  HahnSeries.single (-(eisensteinNumerator ℓ : ℤ)) (1 : ℚ) *
    HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ) *
    (qExpand ℚ ℓ (HahnSeries.ofPowerSeries ℤ ℚ (etaProdPow ℓ)))⁻¹

end Series

def SharpUnitInvariant : Prop :=
  ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, sharpUnitFun ℓ (γ • τ) = sharpUnitFun ℓ τ

def SharpUnitNecessary : Prop :=
  ∀ (m : ℕ) (H : UpperHalfPlane → ℂ), 0 < m → Continuous H →
    (∀ τ : UpperHalfPlane, H τ ^ (ℓ - 1) =
      (ModularForm.discriminant τ /
        ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)) ^ m) →
    (∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, H (γ • τ) = H τ) →
    eisensteinNumerator ℓ ∣ m

end ModularCurve

end

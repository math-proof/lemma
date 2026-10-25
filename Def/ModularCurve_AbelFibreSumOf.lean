import Mathlib
import Lemma.ModularCurve.PeriodOf
import Def.ModularCurve_AbelFibreSum

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve

variable (Γ : Subgroup SL(2, ℤ))

def orbifoldIndexOf (τ : ℍ) : ℕ :=
  Nat.card (MulAction.stabilizer
    (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) / 2

def abelFibreSumOf (F : ℍ → ℂ) (t : ℂ) : Module.Dual ℂ (CuspForm Γ 2) :=
  ∑ᶠ ξ : Quotient (MulAction.orbitRel Γ ℍ),
    ((valueMultiplicity F t ξ.out : ℂ) / (orbifoldIndexOf Γ ξ.out : ℂ)) •
      periodAlongOf Γ UpperHalfPlane.I ξ.out

end ModularCurve

end

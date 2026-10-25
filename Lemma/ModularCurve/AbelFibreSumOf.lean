import Mathlib
import Lemma.ModularCurve.PeriodOf
import Lemma.ModularCurve.AbelFibreSum
import Def.ModularCurve_AbelFibreSumOf

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve

variable (Γ : Subgroup SL(2, ℤ))


theorem orbifoldIndexOf_def (τ : ℍ) :
    orbifoldIndexOf Γ τ =
      Nat.card (MulAction.stabilizer
        (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) / 2 :=
  rfl

theorem abelFibreSumOf_def (F : ℍ → ℂ) (t : ℂ) :
    abelFibreSumOf Γ F t =
      ∑ᶠ ξ : Quotient (MulAction.orbitRel Γ ℍ),
        ((valueMultiplicity F t ξ.out : ℂ) / (orbifoldIndexOf Γ ξ.out : ℂ)) •
          periodAlongOf Γ UpperHalfPlane.I ξ.out :=
  rfl

end ModularCurve

end

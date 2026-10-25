import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Order

set_option autoImplicit false

set_option maxHeartbeats 800000

noncomputable section

open PowerSeries


namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def wSubst (w : R⟦X⟧) : R⟦X⟧ :=
  X ^ 3 + C W.a₁ * (X * w) + C W.a₂ * (X ^ 2 * w) + C W.a₃ * w ^ 2
    + C W.a₄ * (X * w ^ 2) + C W.a₆ * w ^ 3

def wIter : ℕ → R⟦X⟧
  | 0 => 0
  | k + 1 => W.wSubst (wIter k)


def formalW : R⟦X⟧ := PowerSeries.mk fun n => coeff n (W.wIter n)


def wUnitFactor : R⟦X⟧ :=
  1 - (C W.a₁ * X + C W.a₂ * X ^ 2 + C W.a₃ * W.formalW + C W.a₄ * (X * W.formalW)
    + C W.a₆ * W.formalW ^ 2)

end WeierstrassCurve

end

noncomputable section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable def fgW₁ : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) W.formalW

noncomputable def fgSlope : MvPowerSeries (Fin 2) R :=
  fun d => PowerSeries.coeff (d 0 + d 1 + 1) W.formalW

noncomputable def fgNu : MvPowerSeries (Fin 2) R :=
  W.fgW₁ - W.fgSlope * MvPowerSeries.X (0 : Fin 2)

noncomputable def fgZ3Denom : MvPowerSeries (Fin 2) R :=
  1 + MvPowerSeries.C W.a₂ * W.fgSlope
    + MvPowerSeries.C W.a₄ * W.fgSlope ^ 2
    + MvPowerSeries.C W.a₆ * W.fgSlope ^ 3

noncomputable def fgZ3Num : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.C W.a₁ * W.fgSlope
    + MvPowerSeries.C W.a₃ * W.fgSlope ^ 2
    - MvPowerSeries.C W.a₂ * W.fgNu
    - MvPowerSeries.C (2 * W.a₄) * (W.fgSlope * W.fgNu)
    - MvPowerSeries.C (3 * W.a₆) * (W.fgSlope ^ 2 * W.fgNu)

noncomputable def fgZ3 : MvPowerSeries (Fin 2) R :=
  - MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)
    + W.fgZ3Num * MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ)

noncomputable def fgInvDenom : R⟦X⟧ :=
  1 - PowerSeries.C W.a₁ * PowerSeries.X - PowerSeries.C W.a₃ * W.formalW

noncomputable def fgInv : R⟦X⟧ :=
  - PowerSeries.X * PowerSeries.invOfUnit W.fgInvDenom (1 : Rˣ)

noncomputable def formalGroupLaw : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst W.fgZ3 W.fgInv

end WeierstrassCurve

end


noncomputable section

open PowerSeries MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

noncomputable def fgZ3NumFixed : MvPowerSeries (Fin 2) R :=
  - ( MvPowerSeries.C W.a₁ * W.fgSlope
    + MvPowerSeries.C W.a₃ * W.fgSlope ^ 2
    + MvPowerSeries.C W.a₂ * W.fgNu
    + MvPowerSeries.C (2 * W.a₄) * (W.fgSlope * W.fgNu)
    + MvPowerSeries.C (3 * W.a₆) * (W.fgSlope ^ 2 * W.fgNu) )

noncomputable def fgZ3Fixed : MvPowerSeries (Fin 2) R :=
  - MvPowerSeries.X (0 : Fin 2) - MvPowerSeries.X (1 : Fin 2)
    + W.fgZ3NumFixed * MvPowerSeries.invOfUnit W.fgZ3Denom (1 : Rˣ)

noncomputable def formalGroupLawFixed : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst W.fgZ3Fixed W.fgInv

end WeierstrassCurve

end

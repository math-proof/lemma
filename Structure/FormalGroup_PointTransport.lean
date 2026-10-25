import Mathlib
import Def.FormalGroup_NSeries

set_option autoImplicit false

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]

def LawHom.substX (i : Fin 2) (φ : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) φ

structure LawHom (F G : FormalGroup R) where

  series : PowerSeries R

  constantCoeff_series : PowerSeries.constantCoeff series = 0

  comm : PowerSeries.subst F.toPowerSeries series =
    MvPowerSeries.subst ![LawHom.substX 0 series, LawHom.substX 1 series] G.toPowerSeries

structure LawIso (F G : FormalGroup R) extends LawHom F G where

  isUnit_coeff_one : IsUnit (PowerSeries.coeff 1 series)

namespace LawHom

variable {F G : FormalGroup R}


end LawHom


end FormalGroup

end

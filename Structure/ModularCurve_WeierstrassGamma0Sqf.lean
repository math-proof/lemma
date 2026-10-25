import Mathlib
import Structure.ModularCurve_WeierstrassLevelCarrier
import Structure.ModularCurve_WeierstrassLevelModuliDatum
import Structure.ModularCurve_WeierstrassLevelComponents
import Structure.WeierstrassCurve_DrinfeldBasisGlobal
import Def.WeierstrassCurve_DrinfeldTransportPin
import Def.WeierstrassCurve_SectionAtOrigin
import Structure.WeierstrassCurve_DrinfeldLevelFunctor

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace WeierstrassCurve

variable {T : Type u} [CommRing T] (W : WeierstrassCurve T)

structure IsTwoKernel (h : T[X]) : Prop where
  natDegree_le : h.natDegree ≤ 1
  coeff_eq_one : h.coeff 1 = 1
  dvd_Ψ₂Sq : h ∣ W.Ψ₂Sq


end WeierstrassCurve

namespace ModularCurve

variable {T : Type u} [CommRing T]


end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal


end WeierstrassCurve.DrinfeldGlobal

end

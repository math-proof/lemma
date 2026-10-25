import Mathlib
import Structure.ModularCurve_WeierstrassLevelCarrier
import Structure.ModularCurve_WeierstrassLevelModuliDatum
import Structure.ModularCurve_WeierstrassLevelComponents
import Structure.ModularCurve_WeierstrassGamma0Sqf
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

structure IsCyclicGenKernel (p k : ℕ) (h : T[X]) : Prop where

  natDegree_le : h.natDegree ≤ Nat.totient (p ^ k) / 2

  coeff_eq_one : h.coeff (Nat.totient (p ^ k) / 2) = 1

  mul_preΨ_dvd : h * W.preΨ (p ^ (k - 1)) ∣ W.preΨ (p ^ k)

  dvd_smulNumerator : ∀ a : ℕ, 2 ≤ a → a ≤ (p ^ k - 1) / 2 → ¬ p ∣ a →
    h ∣ W.smulNumerator a (Nat.totient (p ^ k) / 2) h


end WeierstrassCurve

namespace ModularCurve

variable {T : Type u} [CommRing T]


end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal


end WeierstrassCurve.DrinfeldGlobal

end

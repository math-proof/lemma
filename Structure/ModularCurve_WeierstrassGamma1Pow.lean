import Mathlib
import Structure.ModularCurve_WeierstrassGamma0Pow

set_option autoImplicit false

universe u

namespace ModularCurve

structure IsGamma1Point {A : Type u} [CommRing A] (W : WeierstrassCurve A) (ℓ : ℕ) (D : LevelPData A) : Prop where

  equation_P : W.toAffine.Equation D.xP D.yP

  preΨ_P : (W.preΨ ℓ).eval D.xP = 0

  xQ_eq : D.xQ = D.xP

  yQ_eq : D.yQ = D.yP

namespace IsGamma1Point

variable {A : Type u} {B : Type u} [CommRing A] [CommRing B] {W : WeierstrassCurve A} {ℓ : ℕ} {D : LevelPData A}


end IsGamma1Point


end ModularCurve

namespace WeierstrassCurve.DrinfeldGlobal


end WeierstrassCurve.DrinfeldGlobal

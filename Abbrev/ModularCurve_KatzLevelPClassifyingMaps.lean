import Mathlib
import Instance.ModularCurve_KatzLevelP
import Instance.ModularCurve_KatzLevelPUniversal

set_option autoImplicit false

universe u v w

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

section TorsionPointLift

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ) {T : Type v} [CommRing T]
  (φ : B →+* T) (x y : T)

end TorsionPointLift

section BasisRingLift

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ) {T : Type v} [CommRing T]
  (φ : B →+* T) (D : LevelPData T) (hD : IsLevelPStructure (W.map φ) p D)

end BasisRingLift

section Univ

variable (p : ℕ) {T : Type v} [CommRing T]

end Univ

section VC

variable (p : ℕ)

abbrev VCPoly : Type := MvPolynomial (Fin 4) (UnivBasisRing p)

end VC

section Borel

variable (p : ℕ) (a : ℕ)

end Borel

end LevelP

end ModularCurve

end

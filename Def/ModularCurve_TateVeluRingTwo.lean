import Mathlib
import Def.ModularCurve_TateVeluRing
import Def.WeierstrassCurve_VeluOrderTwo
import Lemma.WeierstrassCurve.VeluPointMap2

set_option autoImplicit false

noncomputable section

open ModularCurve WeierstrassCurve

namespace ModularCurve.TateVeluRing

section Velu2R

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A)

noncomputable def velu2XR (x₀ y₀ x : A) : A := x + W.veluGx x₀ y₀ * Ring.inverse (x - x₀)

noncomputable def velu2YR (x₀ y₀ x y : A) : A :=
  y - W.veluGx x₀ y₀ * (W.a₁ * (x - x₀) + y - y₀) * Ring.inverse (x - x₀) ^ 2

end Velu2R

end ModularCurve.TateVeluRing

end

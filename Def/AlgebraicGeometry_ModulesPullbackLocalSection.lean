import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (φ : X ⟶ Y)

section

variable {L : Y.Modules} {U : Y.Opens}

def pullbackLocalSection (s : Γ(L, U)) : Γ((Modules.pullback φ).obj L, φ ⁻¹ᵁ U) :=
  ((Modules.pullbackPushforwardAdjunction φ).unit.app L).app U s

end

end AlgebraicGeometry.Scheme.Modules

end

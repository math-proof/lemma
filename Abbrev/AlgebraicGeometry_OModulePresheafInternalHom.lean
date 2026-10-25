import Mathlib

import Structure.AlgebraicGeometry_OModulePresheafHom

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F G : OModulePresheaf π)

abbrev AffBelow (U : V.Opens) : Type u := {W : V.affineOpens // W.1 ≤ U}

abbrev HomPi (U : V.Opens) : Type u := ∀ W : AffBelow U, F.obj W.1.1 →ₗ[R] G.obj W.1.1


end OModulePresheaf

end AlgebraicGeometry

end

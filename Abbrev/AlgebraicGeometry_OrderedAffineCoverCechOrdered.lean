import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Lemma.AlgebraicGeometry.OrderedAffineCoverCechCup
import Lemma.AlgebraicGeometry.OrderedAffineCoverCochainPullback

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

abbrev OIdx (n : ℕ) : Type u := Fin (n + 1) → K.ι

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

end OModulePresheaf

end AlgebraicGeometry

end

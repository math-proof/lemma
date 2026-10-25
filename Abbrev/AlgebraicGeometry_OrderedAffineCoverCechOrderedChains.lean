import Mathlib
import Instance.AlgebraicGeometry_OrderedAffineCoverCech
import Lemma.AlgebraicGeometry.OrderedAffineCoverCechCup
import Lemma.AlgebraicGeometry.OrderedAffineCoverCochainPullback
import Abbrev.AlgebraicGeometry_OrderedAffineCoverCechOrdered

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

abbrev OCh (n : ℕ) : Type u := (K.OIdx n) →₀ ℤ

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

end OModulePresheaf

end AlgebraicGeometry

end

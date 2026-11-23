module

public import Theorem.Scheme.OrderedAffineCoverCechOrdered

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

abbrev OSub {n k : ℕ} (u : K.OIdx n) (t : K.OIdx k) : Prop := ∀ j, ∃ i, u j = t i

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

end OModulePresheaf

end AlgebraicGeometry

end
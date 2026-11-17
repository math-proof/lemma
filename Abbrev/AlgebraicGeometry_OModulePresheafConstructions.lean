module

public import Mathlib

public import Structure.AlgebraicGeometry_OModulePresheafHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}

section KerImCoker

variable {F G : OModulePresheaf π} (φ : Hom F G)

end KerImCoker

section Pushforward

variable {Z : Scheme.{u}} (i : Z ⟶ V)


variable (π) in


variable (π) in

abbrev pushforwardUnit : OModulePresheaf π := pushforward π i (unit (i ≫ π))

end Pushforward

section AffHoms

variable (F : OModulePresheaf π)

end AffHoms


end OModulePresheaf

end AlgebraicGeometry

end

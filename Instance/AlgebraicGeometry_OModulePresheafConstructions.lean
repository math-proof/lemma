module
public import Mathlib
public import Def.AlgebraicGeometry_OModulePresheafHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Theorem.LinearMap.OModulePresheafConstructions
public import Def.AlgebraicGeometry_OModulePresheafConstructions
set_option autoImplicit false


public section

-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_OModulePresheafConstructions.lean: instance decls only.

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {V : Scheme.{u}}


namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}

instance (U : V.Opens) : Subsingleton ((zero π).obj U) := inferInstanceAs (Subsingleton PUnit.{u + 1})


end OModulePresheaf

end AlgebraicGeometry

end

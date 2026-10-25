-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_OModulePresheafConstructions.lean: instance decls only.
import Mathlib

import Def.AlgebraicGeometry_OModulePresheafHom
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Lemma.AlgebraicGeometry.OModulePresheafConstructions

set_option autoImplicit false

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

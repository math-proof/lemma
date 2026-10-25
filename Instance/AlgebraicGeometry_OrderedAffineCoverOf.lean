-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_OrderedAffineCoverOf.lean: instance decls only.
import Mathlib

import Def.AlgebraicGeometry_OModulePresheafHom
import Def.AlgebraicGeometry_OrderedAffineCoverOf

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite

variable {R : Type u} [CommRing R] {V : Scheme.{u}}


namespace Scheme.OrderedAffineCoverOf

variable {W : V.Opens} (K : V.OrderedAffineCoverOf W)

instance (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _
instance (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

end Scheme.OrderedAffineCoverOf


end AlgebraicGeometry

end

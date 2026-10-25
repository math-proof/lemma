import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.Equiv.Defs
import Theorem.Algebra.MonoidAlgebra.InversionTwist
/-!
# Inversion twist of a group-ring module

For a commutative group `G`, inversion induces a ring involution on the group
ring `R[G]`. This file defines both that involution and the module obtained by
precomposing a group-ring action with it.
-/


noncomputable section

namespace GroupRing

variable (R G : Type*) [CommRing R] [CommGroup G]

/-- The inversion twist of a module. Its underlying additive group is a copy
of `A`, while scalars act after applying `GroupRing.inversion`. -/
@[ext]
structure InversionTwist (A : Type*) where
  of ::
  val : A

end GroupRing
end

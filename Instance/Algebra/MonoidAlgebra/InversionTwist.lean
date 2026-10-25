import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.Equiv.Defs
import Def.Algebra.MonoidAlgebra.InversionTwist.Part2
/-!
# Inversion twist of a group-ring module

For a commutative group `G`, inversion induces a ring involution on the group
ring `R[G]`. This file defines both that involution and the module obtained by
precomposing a group-ring action with it.
-/


noncomputable section

namespace GroupRing

variable (R G : Type*) [CommRing R] [CommGroup G]

namespace InversionTwist

variable {R G} {A : Type*} [AddCommGroup A] [Module (MonoidAlgebra R G) A]

instance : AddCommGroup (InversionTwist A) := (equiv A).addCommGroup

instance : SMul (MonoidAlgebra R G) (InversionTwist A) where
  smul r a := of (inversion R G r • a.val)

end InversionTwist
end GroupRing
end

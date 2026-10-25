import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.Equiv.Defs
import Instance.Algebra.MonoidAlgebra.InversionTwist
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

/-- Scalar multiplication in the twist is the original action precomposed
with the group-ring inversion. -/
@[simp]
theorem val_smul (r : MonoidAlgebra R G) (a : InversionTwist A) :
    (r • a).val = inversion R G r • a.val := rfl

end InversionTwist
end GroupRing
end

import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.Equiv.Defs
import Instance.Algebra.MonoidAlgebra.InversionTwist.Part2
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

/-- Twisting twice by inversion canonically recovers the original module. -/
def twistTwistEquiv : InversionTwist (InversionTwist A) ≃ₗ[MonoidAlgebra R G] A where
  toFun a := a.val.val
  invFun a := of (of a)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r a := by
    change inversion R G (inversion R G r) • a.val.val = r • a.val.val
    rw [inversion_involution]

end InversionTwist
end GroupRing
end

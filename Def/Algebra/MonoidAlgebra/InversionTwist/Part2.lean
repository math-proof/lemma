import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.Equiv.Defs
import Structure.Algebra.MonoidAlgebra.InversionTwist
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

/-- The canonical equivalence between an inversion twist and its underlying type. -/
def equiv (A : Type*) : InversionTwist A ≃ A where
  toFun := val
  invFun := of
  left_inv _ := rfl
  right_inv _ := rfl

end InversionTwist
end GroupRing
end

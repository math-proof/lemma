import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.Equiv.Defs
/-!
# Inversion twist of a group-ring module

For a commutative group `G`, inversion induces a ring involution on the group
ring `R[G]`. This file defines both that involution and the module obtained by
precomposing a group-ring action with it.
-/


noncomputable section

namespace GroupRing

variable (R G : Type*) [CommRing R] [CommGroup G]

/-- The involution on a commutative group ring induced by `g ↦ g⁻¹`. -/
def inversion : MonoidAlgebra R G ≃+* MonoidAlgebra R G :=
  MonoidAlgebra.mapDomainRingEquiv R (MulEquiv.inv G)

end GroupRing
end

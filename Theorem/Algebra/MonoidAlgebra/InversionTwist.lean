import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.Equiv.Defs
import Def.Algebra.MonoidAlgebra.InversionTwist
/-!
# Inversion twist of a group-ring module

For a commutative group `G`, inversion induces a ring involution on the group
ring `R[G]`. This file defines both that involution and the module obtained by
precomposing a group-ring action with it.
-/


noncomputable section

namespace GroupRing

variable (R G : Type*) [CommRing R] [CommGroup G]

/-- The group-ring involution sends the basis element at `g` to the basis
element at `g⁻¹`, without changing its coefficient. -/
@[simp]
theorem inversion_single (g : G) (r : R) :
    inversion R G (MonoidAlgebra.single g r) = MonoidAlgebra.single g⁻¹ r := by
  simp [inversion]

/-- Applying the group-ring inversion twice is the identity. -/
@[simp]
theorem inversion_involution (x : MonoidAlgebra R G) :
    inversion R G (inversion R G x) = x := by
  ext g
  simp [inversion]

end GroupRing
end

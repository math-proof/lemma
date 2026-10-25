import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Module.Equiv.Defs
import Theorem.Algebra.MonoidAlgebra.InversionTwist.Part2
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

instance : Module (MonoidAlgebra R G) (InversionTwist A) where
  one_smul a := by
    ext
    change inversion R G 1 • a.val = a.val
    simp
  mul_smul r s a := by
    ext
    change inversion R G (r * s) • a.val = inversion R G r • inversion R G s • a.val
    simp [mul_smul]
  smul_zero r := by
    ext
    change inversion R G r • (0 : A) = 0
    simp
  smul_add r a b := by
    ext
    change inversion R G r • (a.val + b.val) =
      inversion R G r • a.val + inversion R G r • b.val
    simp
  zero_smul a := by
    ext
    change inversion R G 0 • a.val = 0
    simp
  add_smul r s a := by
    ext
    change inversion R G (r + s) • a.val =
      inversion R G r • a.val + inversion R G s • a.val
    simp [add_smul]

end InversionTwist
end GroupRing
end

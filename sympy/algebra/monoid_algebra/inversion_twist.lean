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

/-- The inversion twist of a module. Its underlying additive group is a copy
of `A`, while scalars act after applying `GroupRing.inversion`. -/
@[ext]
structure InversionTwist (A : Type*) where
  of ::
  val : A

namespace InversionTwist

/-- The canonical equivalence between an inversion twist and its underlying type. -/
def equiv (A : Type*) : InversionTwist A ≃ A where
  toFun := val
  invFun := of
  left_inv _ := rfl
  right_inv _ := rfl

variable {R G} {A : Type*} [AddCommGroup A] [Module (MonoidAlgebra R G) A]

instance : AddCommGroup (InversionTwist A) := (equiv A).addCommGroup

instance : SMul (MonoidAlgebra R G) (InversionTwist A) where
  smul r a := of (inversion R G r • a.val)

/-- Scalar multiplication in the twist is the original action precomposed
with the group-ring inversion. -/
@[simp]
theorem val_smul (r : MonoidAlgebra R G) (a : InversionTwist A) :
    (r • a).val = inversion R G r • a.val := rfl

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

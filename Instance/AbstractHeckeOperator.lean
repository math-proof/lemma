-- Carved from Lemma/Definitions/Def_AbstractHeckeOperator.lean: instance decls only.
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.GroupAction.Quotient

section

namespace FixedPoints

open MulAction

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G}

instance : AddCommMonoid (fixedPoints G A) :=
  AddSubmonoid.toAddCommMonoid (FixedPoints.addSubmonoid G A)


variable {R : Type*}

instance [SMul R A] [SMulCommClass G R A] :
    SMul R (fixedPoints G A) where
  smul r a := ⟨r • a.1, fun g ↦ by rw [smul_comm, a.2]⟩

instance [Monoid R] [MulAction R A] [SMulCommClass G R A] :
    MulAction R (fixedPoints G A) where
  one_smul a := Subtype.ext (one_smul _ _)
  mul_smul r s a := Subtype.ext (mul_smul _ _ _)

instance module [Ring R] [Module R A] [SMulCommClass G R A] : Module R (fixedPoints G A) where
  one_smul a := one_smul _ _
  mul_smul r s a := mul_smul _ _ _
  smul_zero a := by
    ext
    exact smul_zero _
  smul_add r s a := by
    ext
    exact smul_add _ _ _
  add_smul r s a := by
    ext
    exact add_smul _ _ _
  zero_smul a := by
    ext
    exact zero_smul _ _

end FixedPoints

open scoped Pointwise


end

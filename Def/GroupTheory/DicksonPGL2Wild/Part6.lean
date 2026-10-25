/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theorem.GroupTheory.DicksonPGL2Tame.Part4
import Lemma.Nat.Card_Stabilizer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Theorem.GroupTheory.DicksonPGL2Wild.Part3
/-!
# Dickson's classification in the wild case

This file classifies finite subgroups of `PGL₂` over an algebraic closure of an odd finite
field when the characteristic divides the group order. It also supplies the projective linear
group order formulas and characteristic-order element facts used by the classification.
-/


namespace MetaMathlibExt

namespace Dickson

open scoped BigOperators Pointwise Polynomial

namespace DicksonWildAffine

noncomputable def borelMulEquivAffine {F : Type*} [Field F] : borel F ≃* Aff F :=
  MulEquiv.ofBijective toAff ⟨toAff_injective, toAff_surjective⟩

def rightRestrict {F : Type*} [Field F] (H : Subgroup (Aff F)) : H →* Fˣ :=
  SemidirectProduct.rightHom.comp H.subtype

def kernelLeft {F : Type*} [Field F] (H : Subgroup (Aff F)) :
    (rightRestrict H).ker →* Multiplicative F where
  toFun z := (z.1.1 : Aff F).left
  map_one' := rfl
  map_mul' x y := by
    change (x.1.1 * y.1.1 : Aff F).left =
      (x.1.1 : Aff F).left * (y.1.1 : Aff F).left
    rw [SemidirectProduct.mul_left]
    have hx : (x.1.1 : Aff F).right = 1 := x.2
    simp [hx, unitAction]

def kernelGamma {F : Type*} [Field F] (H : Subgroup (Aff F)) :
    Additive (rightRestrict H).ker →+ F :=
  (AddEquiv.additiveMultiplicative F).toAddMonoidHom.comp
    (kernelLeft H).toAdditive

def translationAddSubgroup {F : Type*} [Field F]
    (H : Subgroup (Aff F)) : AddSubgroup F :=
  (kernelGamma H).range

noncomputable def multiplierSubfield {F : Type*} [Field F]
    (Γ : AddSubgroup F) [Finite Γ] : Subfield F where
  carrier := {a | ∀ x ∈ Γ, a * x ∈ Γ}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb x hx
    rw [add_mul]
    exact Γ.add_mem (ha x hx) (hb x hx)
  mul_mem' := by
    intro a b ha hb x hx
    rw [mul_assoc]
    exact ha _ (hb x hx)
  neg_mem' := by
    intro a ha x hx
    rw [neg_mul]
    exact Γ.neg_mem (ha x hx)
  inv_mem' := by
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      simp
    · intro x hx
      let f : Γ → Γ := fun y ↦ ⟨a * y.1, ha y.1 y.2⟩
      have hf : Function.Injective f := by
        intro y z hyz
        apply Subtype.ext
        apply mul_left_cancel₀ ha0
        exact congrArg Subtype.val hyz
      obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x, hx⟩
      have hyval : a * y.1 = x := congrArg Subtype.val hy
      rw [← hyval]
      simp [ha0, y.2]

end DicksonWildAffine
end Dickson
end MetaMathlibExt

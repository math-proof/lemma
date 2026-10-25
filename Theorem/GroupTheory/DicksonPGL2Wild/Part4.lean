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
import Instance.GroupTheory.DicksonPGL2Wild.Part2
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

lemma rightRestrict_range_mem_multiplierSubfield {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H]
    (u : (rightRestrict H).range) :
    (u.1 : F) ∈ multiplierSubfield (translationAddSubgroup H) := by
  obtain ⟨h, hu⟩ := u.2
  rw [← hu]
  rintro x ⟨z, rfl⟩
  let w : (rightRestrict H).ker :=
    ⟨h * z.toMul.1 * h⁻¹, by
      change rightRestrict H (h * z.toMul.1 * h⁻¹) = 1
      rw [map_mul, map_mul, map_inv, z.toMul.2]
      simp⟩
  refine ⟨Additive.ofMul w, ?_⟩
  have hzright : (z.toMul.1.1 : Aff F).right = 1 := z.toMul.2
  change (((h.1 * z.toMul.1.1 * h.1⁻¹ : Aff F).left).toAdd) =
    (h.1 : Aff F).right * (z.toMul.1.1 : Aff F).left.toAdd
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul,
    SemidirectProduct.inv_left, map_inv, MulAut.inv_apply, MulAut.mul_apply,
    toAdd_mul, toAdd_inv]
  rw [hzright]
  dsimp [unitAction]
  simp only [AddEquiv.toMultiplicative_apply_apply,
    AddEquiv.toMultiplicative_apply_symm_apply,
    DistribMulAction.toAddEquiv_apply, DistribMulAction.toAddEquiv_symm_apply,
    toAdd_ofAdd, one_smul, Units.smul_def, smul_eq_mul,
    Units.val_inv_eq_inv_val]
  change (h.1 : Aff F).left.toAdd +
      ((h.1 : Aff F).right : F) * (z.toMul.1.1 : Aff F).left.toAdd +
        -(((h.1 : Aff F).right : F) *
          (((h.1 : Aff F).right : F)⁻¹ * (h.1 : Aff F).left.toAdd)) =
    ((h.1 : Aff F).right : F) * (z.toMul.1.1 : Aff F).left.toAdd
  field_simp
  abel

end DicksonWildAffine
end Dickson
end MetaMathlibExt

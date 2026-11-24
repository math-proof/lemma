module
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Theorem.GroupTheory.DicksonPGL2Tame.Part4
public import Theorem.Nat.Card_Stabilizer
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Group.IsCommutative
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Separable
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Theorem.GroupTheory.DicksonPGL2Wild.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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

noncomputable def multiplierRangeHom {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] :
    (rightRestrict H).range →* (multiplierSubfield (translationAddSubgroup H))ˣ where
  toFun u := Units.mk0
    (⟨(u.1 : F), rightRestrict_range_mem_multiplierSubfield H u⟩ :
      multiplierSubfield (translationAddSubgroup H)) (by
        intro h
        apply u.1.ne_zero
        exact congrArg Subtype.val h)
  map_one' := by
    apply Units.ext
    rfl
  map_mul' _ _ := by
    apply Units.ext
    rfl

noncomputable def multiplierRange {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] :
    Subgroup (multiplierSubfield (translationAddSubgroup H))ˣ :=
  (multiplierRangeHom H).range

end DicksonWildAffine
end Dickson
end MetaMathlibExt

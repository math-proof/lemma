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
import Theorem.GroupTheory.DicksonPGL2Wild.Part4
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

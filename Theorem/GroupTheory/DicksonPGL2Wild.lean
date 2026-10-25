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
import Def.GroupTheory.DicksonPGL2Wild.Part3
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

lemma mk_lift {F : Type*} [Field F]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) :
    Matrix.ProjGenLinGroup.mk (lift g) = g :=
  Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective g)

lemma lift_lowerLeft_eq_zero {F : Type*} [Field F] (g : borel F) :
    (lift g.1 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  classical
  have hg : g.1 • infinity F = infinity F :=
    MulAction.mem_stabilizer_iff.mp g.2
  have hA : lift g.1 • (OnePoint.infty : OnePoint F) = OnePoint.infty := by
    apply (OnePoint.equivProjectivization F).injective
    rw [OnePoint.equivProjectivization_smul]
    rw [← mk_lift g.1] at hg
    simpa [infinity] using hg
  exact OnePoint.smul_infty_eq_self_iff.mp hA

lemma lift_lowerRight_ne_zero {F : Type*} [Field F] (g : borel F) :
    (lift g.1 : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  intro h
  apply (lift g.1).det_ne_zero
  rw [Matrix.det_fin_two, lift_lowerLeft_eq_zero g, h]
  ring

lemma lift_upperLeft_ne_zero {F : Type*} [Field F] (g : borel F) :
    (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
  intro h
  apply (lift g.1).det_ne_zero
  rw [Matrix.det_fin_two, lift_lowerLeft_eq_zero g, h]
  ring

end DicksonWildAffine
end Dickson
end MetaMathlibExt

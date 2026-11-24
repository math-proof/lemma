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
public import Def.GroupTheory.DicksonPGL2Wild.Part3


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

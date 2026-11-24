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
public import Theorem.GroupTheory.DicksonPGL2Wild.Part2


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

noncomputable def toAff {F : Type*} [Field F] : borel F →* Aff F where
  toFun g := ⟨Multiplicative.ofAdd (gamma g), lambda g⟩
  map_one' := by
    ext
    · exact gamma_one (F := F)
    · exact congrArg Units.val (lambda_one (F := F))
  map_mul' g h := by
    ext
    · exact gamma_mul g h
    · exact congrArg Units.val (lambda_mul g h)

noncomputable def affineGL {F : Type*} [Field F] (a : F) (u : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(u : F), a; 0, 1] (by
    simp [Matrix.det_fin_two, Units.ne_zero])

end DicksonWildAffine
end Dickson
end MetaMathlibExt

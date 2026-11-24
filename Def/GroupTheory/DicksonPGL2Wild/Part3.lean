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
public import Abbrev.GroupTheory.DicksonPGL2Wild


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

noncomputable def infinity (F : Type*) [Field F] :
    Projectivization F (Fin 2 → F) := by
  classical
  exact OnePoint.equivProjectivization F OnePoint.infty

noncomputable def borel (F : Type*) [Field F] :
    Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) := by
  classical
  exact MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) (infinity F)

noncomputable def lift {F : Type*} [Field F]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) : GL (Fin 2) F :=
  Classical.choose (Matrix.ProjGenLinGroup.mk_surjective g)

end DicksonWildAffine
end Dickson
end MetaMathlibExt

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
import Abbrev.GroupTheory.DicksonPGL2Wild
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

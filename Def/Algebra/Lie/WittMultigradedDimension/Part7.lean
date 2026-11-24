module
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Def.Algebra.Lie.FreeLieMultihomogeneousComponent
public import Def.Algebra.Lie.WittMultigradedValue
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Rotate
public import Theorem.Combinatorics.Words.LyndonWord.Part14
public import Theorem.Finset.Words.LyndonWord
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeAlgebra
public import Theorem.Algebra.Lie.WittMultigradedDimension.Part7
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/
namespace MetaMathlibExt

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable def wittAssocLift (K : Type) [Field K] {r : ℕ} :
    FreeLieAlgebra K (Fin r) →ₗ⁅K⁆ FreeAlgebra K (Fin r) :=
  FreeLieAlgebra.lift K (FreeAlgebra.ι K)

end MetaMathlibExt

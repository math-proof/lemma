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
public import Theorem.Algebra.Lie.WittMultigradedDimension.Part5
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

noncomputable def wittAssocWord (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) : FreeAlgebra K (Fin r) :=
  FreeAlgebra.basisFreeMonoid K (Fin r) (FreeMonoid.ofList w)

def WittWordsGE {r : ℕ} (w : List (Fin r)) : Set (List (Fin r)) :=
  {z | wittWordContent z = wittWordContent w ∧ w ≤ z}

def WittWordsGT {r : ℕ} (w : List (Fin r)) : Set (List (Fin r)) :=
  {z | wittWordContent z = wittWordContent w ∧ w < z}

noncomputable def wittWordSpanGE (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) : Submodule K (FreeAlgebra K (Fin r)) :=
  Submodule.span K (wittAssocWord K '' WittWordsGE w)

noncomputable def wittWordSpanGT (K : Type) [Field K] {r : ℕ}
    (w : List (Fin r)) : Submodule K (FreeAlgebra K (Fin r)) :=
  Submodule.span K (wittAssocWord K '' WittWordsGT w)

end MetaMathlibExt

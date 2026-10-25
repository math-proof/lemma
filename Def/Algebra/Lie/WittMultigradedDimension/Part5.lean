/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/WittMultigradedDimension.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Dimension.Finite
import Def.Algebra.Lie.FreeLieMultihomogeneousComponent
import Def.Algebra.Lie.WittMultigradedValue
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Rotate
import Theorem.Combinatorics.Words.LyndonWord.Part14
import Lemma.Finset.Words.LyndonWord
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeAlgebra
import Theorem.Algebra.Lie.WittMultigradedDimension.Part5
open scoped BigOperators

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

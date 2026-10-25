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
import Instance.Algebra.Lie.WittMultigradedDimension
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

attribute [local instance 100] LieRing.ofAssociativeRing

def WittLyndonPairRel {r n : ℕ} (p q : WittLyndonPair r n) : Prop :=
  q.1.1 ++ q.1.2 < p.1.1 ++ p.1.2 ∨
    (q.1.1 ++ q.1.2 = p.1.1 ++ p.1.2 ∧ p.1.1.length < q.1.1.length)

end MetaMathlibExt

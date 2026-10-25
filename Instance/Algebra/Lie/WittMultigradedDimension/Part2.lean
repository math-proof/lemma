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
import Def.Algebra.Lie.WittMultigradedDimension.Part10
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

attribute [local instance 100] LieRing.ofAssociativeRing

instance {r n : ℕ} : IsTrans (WittLyndonPair r n) WittLyndonPairRel where
  trans p q s hpq hqs := by
    rcases hpq with hpq | ⟨hpq, hpqlen⟩
    · rcases hqs with hqs | ⟨hqs, _⟩
      · exact Or.inl (hqs.trans hpq)
      · exact Or.inl (hqs ▸ hpq)
    · rcases hqs with hqs | ⟨hqs, hqslen⟩
      · exact Or.inl (hqs.trans_le hpq.le)
      · exact Or.inr ⟨hqs.trans hpq, hpqlen.trans hqslen⟩

instance {r n : ℕ} : Std.Irrefl (@WittLyndonPairRel r n) where
  irrefl p hp := by
    rcases hp with hp | ⟨_, hp⟩
    · exact (lt_irrefl _) hp
    · exact (lt_irrefl _) hp

end MetaMathlibExt

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
import Def.Algebra.Lie.WittMultigradedDimension.Part2
open scoped BigOperators

/-!
# Witt's multigraded dimension formula

This file proves the multigraded dimension formula for a finitely generated free Lie algebra,
using the Lyndon-word basis and the enumeration of Lyndon words with prescribed content.
-/


namespace MetaMathlibExt

theorem wittLongestLyndonSuffixIndex_spec {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) :
    0 < wittLongestLyndonSuffixIndex w hw ∧
      wittLongestLyndonSuffixIndex w hw < w.length ∧
      WittSuffixLyndon (w.drop (wittLongestLyndonSuffixIndex w hw)) := by
  classical
  exact Nat.find_spec (wittExists_lyndonSuffixIndex w hw)

theorem wittLongestLyndonSuffixIndex_min {α : Type*} [LinearOrder α]
    (w : List α) (hw : 2 ≤ w.length) {j : ℕ}
    (hj0 : 0 < j) (hjw : j < w.length) (hj : WittSuffixLyndon (w.drop j)) :
    wittLongestLyndonSuffixIndex w hw ≤ j := by
  classical
  exact Nat.find_min' (wittExists_lyndonSuffixIndex w hw) ⟨hj0, hjw, hj⟩

end MetaMathlibExt

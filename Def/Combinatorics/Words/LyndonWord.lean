/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Algebra.Lie.WittMultigradedValue
import Def.Combinatorics.Words.PrimitiveWord
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.PeriodicityLemma
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

/-- The content of a word: the multiplicity of each letter. -/
def wittWordContent {r : ℕ} (w : List (Fin r)) : Fin r → ℕ :=
  fun i => w.count i

/-- A nonempty word which is strictly smaller than each nontrivial rotation. -/
def IsLyndonWord {α : Type*} [LinearOrder α] (w : List α) : Prop :=
  w ≠ [] ∧ ∀ k, 0 < k → k < w.length → w < w.rotate k

end MetaMathlibExt

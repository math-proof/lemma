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
import Def.Combinatorics.Words.LyndonWord
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

/-- Word content is additive under concatenation. -/
@[simp]
theorem wittWordContent_append {r : ℕ} (u v : List (Fin r)) :
    wittWordContent (u ++ v) = fun i => wittWordContent u i + wittWordContent v i := by
  funext i
  simp [wittWordContent]

/-- Prepending a letter increments its coordinate in the content. -/
@[simp]
theorem wittWordContent_cons {r : ℕ} (i : Fin r) (w : List (Fin r)) :
    wittWordContent (i :: w) =
      Function.update (wittWordContent w) i (wittWordContent w i + 1) := by
  funext j
  by_cases h : j = i
  · subst j
    simp [wittWordContent]
  · simp [wittWordContent, h, Ne.symm h]

/-- The sum of the content of a word is its length. -/
@[simp]
theorem sum_wittWordContent {r : ℕ} (w : List (Fin r)) :
    (∑ i, wittWordContent w i) = w.length := by
  rw [← List.sum_toFinset_count_eq_length w]
  symm
  apply Finset.sum_subset
  · simp
  · intro i _ hi
    exact List.count_eq_zero_of_not_mem (by simpa using hi)

end MetaMathlibExt

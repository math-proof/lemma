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
import Theorem.Combinatorics.Words.LyndonWord.Part13
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

noncomputable def wittWordsRootDataEquiv {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    WordsOfContent degree ≃ WittPrimitiveRootData degree where
  toFun := wittWordToRootData degree hdegree
  invFun := wittRootDataToWord degree
  left_inv := wittRootDataToWord_wordToRootData degree hdegree
  right_inv := wittWordToRootData_rootDataToWord degree hdegree

end MetaMathlibExt

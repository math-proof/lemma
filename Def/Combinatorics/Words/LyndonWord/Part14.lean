module
public import Def.Algebra.Lie.WittMultigradedValue
public import Def.Combinatorics.Words.PrimitiveWord
public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.PeriodicityLemma
public import Theorem.Combinatorics.Words.LyndonWord.Part13
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Def.Algebra.Lie.WittMultigradedValue
public import Def.Combinatorics.Words.PrimitiveWord
public import Mathlib.Data.List.Rotate
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.PeriodicityLemma
public import Theorem.Combinatorics.Words.LyndonWord

@[expose] public section

open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

/-- Words with prescribed content. -/
def WordsOfContent {r : ℕ} (degree : Fin r → ℕ) :=
  {w : List (Fin r) // wittWordContent w = degree}

/-- Lyndon words with prescribed content. -/
def LyndonWordsOfContent {r : ℕ} (degree : Fin r → ℕ) :=
  {w : WordsOfContent degree // IsLyndonWord w.1}

def wittWordsToVector {r : ℕ} (degree : Fin r → ℕ) :
    WordsOfContent degree → List.Vector (Fin r) (∑ i, degree i) :=
  fun w => ⟨w.1, by rw [← sum_wittWordContent, w.2]⟩

end MetaMathlibExt

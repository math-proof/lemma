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
import Theorem.Combinatorics.Words.LyndonWord.Part10
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

def wittRotateLyndon {r : ℕ} (degree : Fin r → ℕ) :
    LyndonWordsOfContent degree × Fin (∑ i, degree i) →
      PrimitiveWordsOfContent degree
  | ⟨w, k⟩ =>
      ⟨⟨w.1.1.rotate k, (wittWordContent_rotate w.1.1 k).trans w.1.2⟩,
        isPrimitiveWord_rotate (isPrimitiveWord_of_isLyndonWord w.2) k⟩

def wittPrimitiveMin {r : ℕ} {degree : Fin r → ℕ}
    (w : PrimitiveWordsOfContent degree) : LyndonWordsOfContent degree :=
  ⟨⟨wittMinRotation w.1.1, (wittWordContent_minRotation w.1.1).trans w.1.2⟩,
    wittMinRotation_isLyndon w.2⟩

noncomputable def wittPrimitiveMinIndex {r : ℕ} {degree : Fin r → ℕ}
    (w : PrimitiveWordsOfContent degree) : Fin (∑ i, degree i) :=
  Fin.cast (length_wordsOfContent w.1) (wittMinRotationIndex w.2)

noncomputable def wittPrimitiveToLyndonRotation {r : ℕ}
    {degree : Fin r → ℕ} (w : PrimitiveWordsOfContent degree) :
    LyndonWordsOfContent degree × Fin (∑ i, degree i) :=
  ⟨wittPrimitiveMin w, wittPrimitiveMinIndex w⟩

end MetaMathlibExt

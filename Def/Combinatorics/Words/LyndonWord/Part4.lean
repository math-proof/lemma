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
import Abbrev.Combinatorics.Words.LyndonWord
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

def wittWordsHeadTail {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) (w : WordsOfContent degree) :
    Σ i : WittPositiveLetter degree, WordsOfContent (wittDegreePred degree i.1) :=
  let h := wittWord_head_tail w hdegree
  ⟨⟨w.1.head (wittWord_ne_nil w hdegree), h.1⟩, ⟨w.1.tail, h.2⟩⟩

def wittWordsCons {r : ℕ} (degree : Fin r → ℕ) :
    (Σ i : WittPositiveLetter degree, WordsOfContent (wittDegreePred degree i.1)) →
      WordsOfContent degree
  | ⟨i, w⟩ => ⟨i.1 :: w.1, by
      rw [wittWordContent_cons, w.2]
      funext j
      by_cases hji : j = i.1
      · subst j
        have hi : 0 < degree i.1 := i.2
        simp only [wittDegreePred, Function.update_self]
        omega
      · simp [wittDegreePred, hji]⟩

def wittWordsConsEquiv {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    WordsOfContent degree ≃
      Σ i : WittPositiveLetter degree, WordsOfContent (wittDegreePred degree i.1) where
  toFun := wittWordsHeadTail degree hdegree
  invFun := wittWordsCons degree
  left_inv w := by
    apply Subtype.ext
    exact List.cons_head_tail (wittWord_ne_nil w hdegree)
  right_inv p := by
    rcases p with ⟨i, w⟩
    rfl

end MetaMathlibExt

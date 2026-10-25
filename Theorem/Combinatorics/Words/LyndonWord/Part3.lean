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
import Def.Combinatorics.Words.LyndonWord.Part3
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem wittWord_ne_nil {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) (hdegree : 0 < ∑ i, degree i) : w.1 ≠ [] := by
  intro hw
  have hzero : (∑ i, degree i) = 0 := by
    rw [← w.2, sum_wittWordContent, hw]
    rfl
  exact (Nat.ne_of_gt hdegree) hzero

theorem wittWord_head_tail {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) (hdegree : 0 < ∑ i, degree i) :
    let i := w.1.head (wittWord_ne_nil w hdegree)
    0 < degree i ∧ wittWordContent w.1.tail = wittDegreePred degree i := by
  let hne := wittWord_ne_nil w hdegree
  let i := w.1.head hne
  have hcontent : wittWordContent (i :: w.1.tail) = degree := by
    rw [List.cons_head_tail hne]
    exact w.2
  rw [wittWordContent_cons] at hcontent
  have hi := congr_fun hcontent i
  constructor
  · simp [i] at hi
    omega
  · funext j
    have hj := congr_fun hcontent j
    by_cases hji : j = i
    · subst j
      simp [wittDegreePred, i] at hi ⊢
      omega
    · simp only [ne_eq, hji, not_false_eq_true, Function.update_of_ne,
        wittDegreePred, i] at hj ⊢
      exact hj

end MetaMathlibExt

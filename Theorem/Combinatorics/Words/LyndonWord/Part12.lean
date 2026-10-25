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
import Def.Combinatorics.Words.LyndonWord.Part12
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem wittGcd_ne_zero {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) : Finset.univ.gcd degree ≠ 0 := by
  rw [Finset.gcd_ne_zero_iff]
  by_contra h
  have hall : ∀ i ∈ Finset.univ, degree i = 0 := by
    intro i hi
    by_contra hne
    exact h ⟨i, hi, hne⟩
  have hzero : (∑ i, degree i) = 0 := Finset.sum_eq_zero hall
  omega

theorem wittDegree_eq_exponent_mul_rootContent {r : ℕ}
    {degree : Fin r → ℕ} (w : WordsOfContent degree)
    (hdegree : 0 < ∑ i, degree i) :
    degree = fun i => wittExponent w.1 (wittWord_ne_nil w hdegree) *
      wittWordContent (wittRoot w.1 (wittWord_ne_nil w hdegree)) i := by
  calc
    degree = wittWordContent w.1 := w.2.symm
    _ = wittWordContent (wittWordPower
        (wittRoot w.1 (wittWord_ne_nil w hdegree))
        (wittExponent w.1 (wittWord_ne_nil w hdegree))) :=
      congr_arg wittWordContent (wittWord_eq_root_power w.1 (wittWord_ne_nil w hdegree))
    _ = _ := wittWordContent_power _ _

theorem wittRoot_content {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) (hdegree : 0 < ∑ i, degree i) :
    wittWordContent (wittRoot w.1 (wittWord_ne_nil w hdegree)) =
      fun i => degree i / wittExponent w.1 (wittWord_ne_nil w hdegree) := by
  let d := wittExponent w.1 (wittWord_ne_nil w hdegree)
  have hd : 0 < d := wittExponent_pos w.1 (wittWord_ne_nil w hdegree)
  have hmul := wittDegree_eq_exponent_mul_rootContent w hdegree
  funext i
  have hi := congr_fun hmul i
  dsimp [d] at hd ⊢
  rw [hi]
  exact (Nat.mul_div_cancel_left _ hd).symm

theorem wittExponent_dvd_gcd {r : ℕ} {degree : Fin r → ℕ}
    (w : WordsOfContent degree) (hdegree : 0 < ∑ i, degree i) :
    wittExponent w.1 (wittWord_ne_nil w hdegree) ∣ Finset.univ.gcd degree := by
  apply Finset.dvd_gcd
  intro i _
  refine ⟨wittWordContent (wittRoot w.1 (wittWord_ne_nil w hdegree)) i, ?_⟩
  exact congr_fun (wittDegree_eq_exponent_mul_rootContent w hdegree) i

end MetaMathlibExt

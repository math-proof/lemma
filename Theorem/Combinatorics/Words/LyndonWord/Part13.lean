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
import Def.Combinatorics.Words.LyndonWord.Part13
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem wittRootDataToWord_wordToRootData {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) (w : WordsOfContent degree) :
    wittRootDataToWord degree (wittWordToRootData degree hdegree w) = w := by
  apply Subtype.ext
  change wittWordPower
      (wittRoot w.1 (wittWord_ne_nil w hdegree))
      (wittExponent w.1 (wittWord_ne_nil w hdegree)) = w.1
  exact (wittWord_eq_root_power w.1 (wittWord_ne_nil w hdegree)).symm

theorem wittPrimitiveWords_heq_of_word_eq {r : ℕ} {a b : Fin r → ℕ}
    {u : PrimitiveWordsOfContent a} {v : PrimitiveWordsOfContent b}
    (h : u.1.1 = v.1.1) : HEq u v := by
  have hab : a = b := by
    rw [← u.1.2, ← v.1.2, h]
  subst b
  apply heq_of_eq
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem wittWordToRootData_rootDataToWord {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) (p : WittPrimitiveRootData degree) :
    wittWordToRootData degree hdegree (wittRootDataToWord degree p) = p := by
  rcases p with ⟨⟨d, hdmem⟩, u⟩
  have hdg := (Nat.mem_divisors.mp hdmem).1
  have hgpos : 0 < Finset.univ.gcd degree :=
    Nat.pos_of_ne_zero (wittGcd_ne_zero degree hdegree)
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdg hgpos
  dsimp only [wittWordToRootData, wittRootDataToWord]
  have he : wittExponent (wittWordPower u.1.1 d) _ = d :=
    wittExponent_power_of_primitive u.2 hd
  apply Sigma.ext
  · exact Subtype.ext he
  · apply wittPrimitiveWords_heq_of_word_eq
    exact wittRoot_power_of_primitive u.2 hd

end MetaMathlibExt

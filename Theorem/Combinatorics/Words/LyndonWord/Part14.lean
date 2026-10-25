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
import Def.Combinatorics.Words.LyndonWord.Part14
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

theorem card_primitiveWords_eq_moebius_sum {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) :
    (Fintype.card (PrimitiveWordsOfContent degree) : ℤ) =
      ∑ d ∈ Nat.divisors (Finset.univ.gcd degree),
        ArithmeticFunction.moebius d *
          (Nat.multinomial Finset.univ (fun i => degree i / d) : ℤ) := by
  let g := Finset.univ.gcd degree
  let A : ℕ → ℤ := fun n =>
    Fintype.card (PrimitiveWordsOfContent (fun i => degree i / (g / n)))
  let C : ℕ → ℤ := fun n =>
    Fintype.card (WordsOfContent (fun i => degree i / (g / n)))
  have hg0 : g ≠ 0 := wittGcd_ne_zero degree hdegree
  have hgpos : 0 < g := Nat.pos_of_ne_zero hg0
  have hpremise : ∀ n > 0, n ∈ {n : ℕ | n ∣ g} →
      (∑ i ∈ n.divisors, A i) = C n := by
    intro n hn hnG
    let k := g / n
    let beta : Fin r → ℕ := fun i => degree i / k
    have hkG : k ∣ g := Nat.div_dvd_of_dvd hnG
    have hk0 : 0 < k := Nat.div_pos (Nat.le_of_dvd hgpos hnG) hn
    have hkdegree : ∀ i, k ∣ degree i := fun i =>
      hkG.trans (Finset.gcd_dvd (Finset.mem_univ i))
    have hbeta : 0 < ∑ i, beta i := wittSum_div_pos degree hdegree hk0 hkdegree
    have hgcdBeta : Finset.univ.gcd beta = n := by
      dsimp [beta]
      rw [wittGcd_div degree hkG]
      exact Nat.div_div_self hnG hg0
    have hcard := card_words_eq_sum_primitive beta hbeta
    rw [hgcdBeta] at hcard
    have hnat :
        (∑ i ∈ n.divisors,
          Fintype.card (PrimitiveWordsOfContent (fun j => degree j / (g / i)))) =
          Fintype.card (WordsOfContent beta) := by
      calc
        (∑ i ∈ n.divisors,
            Fintype.card (PrimitiveWordsOfContent (fun j => degree j / (g / i)))) =
            ∑ e ∈ n.divisors,
              Fintype.card (PrimitiveWordsOfContent
                (fun j => degree j / (g / (n / e)))) := by
          symm
          exact Nat.sum_div_divisors n fun i =>
            Fintype.card (PrimitiveWordsOfContent (fun j => degree j / (g / i)))
        _ = ∑ e ∈ n.divisors,
              Fintype.card (PrimitiveWordsOfContent (fun j => beta j / e)) := by
          apply Finset.sum_congr rfl
          intro e he
          have heN : e ∣ n := Nat.dvd_of_mem_divisors he
          have hden : g / (n / e) = k * e := by
            calc
              g / (n / e) = (k * n) / (n / e) := by
                congr 1
                exact (Nat.div_mul_cancel hnG).symm
              _ = k * (n / (n / e)) := Nat.mul_div_assoc k (Nat.div_dvd_of_dvd heN)
              _ = k * e := by rw [Nat.div_div_self heN hn.ne']
          have hfun : (fun j => degree j / (g / (n / e))) =
              (fun j => beta j / e) := by
            funext j
            dsimp [beta]
            rw [hden, Nat.div_div_eq_div_mul]
          rw [hfun]
        _ = Fintype.card (WordsOfContent beta) := hcard.symm
    change (∑ i ∈ n.divisors,
      (Fintype.card (PrimitiveWordsOfContent (fun j => degree j / (g / i))) : ℤ)) =
        (Fintype.card (WordsOfContent beta) : ℤ)
    exact_mod_cast hnat
  have hinversion :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on
      {n : ℕ | n ∣ g} (fun _ _ hmn hnG => hmn.trans hnG)).mp hpremise g hgpos
      (dvd_refl g)
  calc
    (Fintype.card (PrimitiveWordsOfContent degree) : ℤ) = A g := by
      simp [A, Nat.div_self hgpos]
    _ = ∑ x ∈ g.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℤ) * C x.2 := hinversion.symm
    _ = ∑ d ∈ g.divisors,
        ArithmeticFunction.moebius d * C (g / d) := by
      exact Nat.sum_divisorsAntidiagonal fun d e =>
        ArithmeticFunction.moebius d * C e
    _ = ∑ d ∈ g.divisors,
        ArithmeticFunction.moebius d *
          (Nat.multinomial Finset.univ (fun i => degree i / d) : ℤ) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdG : d ∣ g := Nat.dvd_of_mem_divisors hd
      congr 1
      dsimp [C]
      rw [Nat.div_div_self hdG hg0]
      exact_mod_cast card_wordsOfContent_eq_multinomial (fun i => degree i / d)

/-- The number of Lyndon words with prescribed positive content is Witt's multigraded value. -/
theorem card_lyndonWordsOfContent_eq_wittMultigradedValue {r : ℕ}
    (degree : Fin r → ℕ) (hdegree : 0 < ∑ i, degree i) :
    (Fintype.card (LyndonWordsOfContent degree) : ℚ) = wittMultigradedValue degree := by
  let n := ∑ i, degree i
  have hn : 0 < n := hdegree
  have hmobZ := card_primitiveWords_eq_moebius_sum degree hdegree
  have hmobQ :
      (Fintype.card (PrimitiveWordsOfContent degree) : ℚ) =
        ∑ d ∈ Nat.divisors (Finset.univ.gcd degree),
          ((ArithmeticFunction.moebius d : ℤ) : ℚ) *
            (Nat.multinomial Finset.univ (fun i => degree i / d) : ℚ) := by
    exact_mod_cast hmobZ
  have horbit :
      (Fintype.card (PrimitiveWordsOfContent degree) : ℚ) =
        (n : ℚ) * Fintype.card (LyndonWordsOfContent degree) := by
    exact_mod_cast card_primitiveWords_eq_mul_lyndonWords degree
  rw [wittMultigradedValue]
  change (Fintype.card (LyndonWordsOfContent degree) : ℚ) =
    if n = 0 then 0 else (1 / (n : ℚ)) * _
  rw [ite_eq_right hn.ne']
  rw [← hmobQ, horbit]
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ hnq, one_mul]

end MetaMathlibExt

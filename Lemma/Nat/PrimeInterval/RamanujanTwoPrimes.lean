import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeInterval.Breusch
import Lemma.Nat.PrimeInterval.Breusch


namespace MathlibExt.NumberTheory.BreuschWanted

/--
[ramanujan_two_primes_between](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/RamanujanTwoPrimes.lean)
-/
@[path]
lemma ramanujan_two_primes_between
  {n : ℕ}
-- given
  (hn : 6 ≤ n) :
-- imply
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n < p ∧ p < q ∧ q < 2 * n := by
-- proof
  by_cases h48 : 48 ≤ n
  · obtain ⟨p, hp_prime, hn_p, hp_upper⟩ :=
    breusch_prime_interval (n : ℝ) (by exact_mod_cast h48)
    have hscaled : (48 : ℝ) ≤ (9 / 8 : ℝ) * n := by
      have hn_real : (48 : ℝ) ≤ n := by exact_mod_cast h48
      nlinarith
    obtain ⟨q, hq_prime, hscaled_q, hq_upper⟩ :=
      breusch_prime_interval ((9 / 8 : ℝ) * n) hscaled
    refine ⟨p, q, hp_prime, hq_prime, ?_, ?_, ?_⟩
    · exact_mod_cast hn_p
    · exact_mod_cast hp_upper.trans hscaled_q
    · have hn_pos : (0 : ℝ) < n := by positivity
      have hq_two : (q : ℝ) < 2 * n := by
        calc
          (q : ℝ) < (9 / 8 : ℝ) * ((9 / 8 : ℝ) * n) := hq_upper
          _ < 2 * n := by nlinarith
      exact_mod_cast hq_two
  · have hn_lt : n < 48 := Nat.lt_of_not_ge h48
    by_cases h7 : n < 7
    · exact ⟨7, 11, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h11 : n < 11
    · exact ⟨11, 13, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h13 : n < 13
    · exact ⟨13, 17, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h17 : n < 17
    · exact ⟨17, 19, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h23 : n < 23
    · exact ⟨23, 29, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h29 : n < 29
    · exact ⟨29, 31, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h37 : n < 37
    · exact ⟨37, 41, by decide, by decide, by omega, by omega, by omega⟩
    by_cases h43 : n < 43
    · exact ⟨43, 47, by decide, by decide, by omega, by omega, by omega⟩
    exact ⟨53, 59, by decide, by decide, by omega, by omega, by omega⟩

end MathlibExt.NumberTheory.BreuschWanted


-- created on 2026-10-20
-- updated on 2026-10-23

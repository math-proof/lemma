import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.ConsecutivePrime


namespace MetaMathlibExt

/--
[prime_sub_primorial_prime_of_between_consecutive_primes_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeGapsNearPrimorials.lean)
-/
@[path]
lemma prime_sub_primorial_prime_of_between_consecutive_primes_general
  {q r p : ℕ}
-- given
  (hconsecutive : ∀ s : ℕ, q < s → s < r → ¬ Nat.Prime s)
  (hp : Nat.Prime p)
  (hlower : primorial q + 1 < p)
  (hupper : p < primorial q + r ^ 2) :
-- imply
  Nat.Prime (p - primorial q) := by
-- proof
  have hNpos : 0 < primorial q := primorial_pos q
  have hNp : primorial q < p := by omega
  have hd2 : 2 ≤ p - primorial q := by omega
  have hplt : p - primorial q < r ^ 2 := by omega
  have hpeq : primorial q + (p - primorial q) = p :=
    Nat.add_sub_cancel' (le_of_lt hNp)
  have key : ∀ t : ℕ, Nat.Prime t → t ∣ (p - primorial q) → r ≤ t := by
    intro t ht htd
    by_contra! hlt
    obtain hsq | hsq := le_or_gt t q
    · have htN : t ∣ primorial q := (ht.dvd_primorial_iff).mpr hsq
      have htp : t ∣ p := by
        have hadd : t ∣ primorial q + (p - primorial q) := Nat.dvd_add htN htd
        rwa [hpeq] at hadd
      obtain h1 | h1 := (Nat.dvd_prime hp).mp htp
      · exact ht.ne_one h1
      · have htle : t ≤ primorial q := Nat.le_of_dvd hNpos htN
        omega
    · exact hconsecutive t hsq hlt ht
  rw [Nat.prime_def_le_sqrt]
  refine ⟨hd2, fun m hm2 hmsqrt hmdvd => ?_⟩
  obtain ⟨t, htprime, htm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  have htd : t ∣ (p - primorial q) := dvd_trans htm hmdvd
  have htm_le : t ≤ m := Nat.le_of_dvd (by omega : 0 < m) htm
  have hmm : m * m ≤ p - primorial q := Nat.le_sqrt.mp hmsqrt
  have hlt_mm : m * m < r * r := by
    calc m * m ≤ p - primorial q := hmm
    _ < r ^ 2 := hplt
    _ = r * r := pow_two r
  have hmr : m < r := by
    by_contra! hcon
    have hle : r * r ≤ m * m := Nat.mul_le_mul hcon hcon
    omega
  have htr : t < r := lt_of_le_of_lt htm_le hmr
  have hle := key t htprime htd
  omega
set_option linter.unusedVariables false in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prime_sub_primorial_prime_of_between_consecutive_primes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeGapsNearPrimorials.lean)
-/
@[path]
lemma prime_sub_primorial_prime_of_between_consecutive_primes
  {q r p : ℕ}
-- given
  (hq : Nat.Prime q)
  (hr : Nat.Prime r)
  (hqr : q < r)
  (hconsecutive : ∀ s : ℕ, q < s → s < r → ¬ Nat.Prime s)
  (hp : Nat.Prime p)
  (hlower : primorial q + 1 < p)
  (hupper : p < primorial q + r ^ 2) :
-- imply
  Nat.Prime (p - primorial q) :=
-- proof
prime_sub_primorial_prime_of_between_consecutive_primes_general hconsecutive hp hlower hupper

end MetaMathlibExt

namespace MetaMathlibExt

/--
[AreConsecutivePrimes.prime_sub_primorial_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeGapsNearPrimorials.lean)
-/
@[path]
lemma AreConsecutivePrimes.prime_sub_primorial_prime
  {q r p : ℕ}
-- given
  (hqr : AreConsecutivePrimes q r)
  (hp : Nat.Prime p)
  (hlower : primorial q + 1 < p)
  (hupper : p < primorial q + r ^ 2) :
-- imply
  Nat.Prime (p - primorial q) :=
-- proof
  prime_sub_primorial_prime_of_between_consecutive_primes_general
    (fun s hqs hsr hs => (hqr.2.2.2 s hs).elim (fun h => by omega) (fun h => by omega)) hp hlower hupper

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26

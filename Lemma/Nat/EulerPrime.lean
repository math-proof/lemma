import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.EulerPrime
open MetaMathlibExt


namespace MetaMathlibExt

/-!
[prod_odd_of_all_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
# Euler primes of odd perfect numbers
Source: Dris, JIS VOL15, <https://cs.uwaterloo.ca/journals/JIS/VOL15/Dris/dris8.tex>,
SHA-256 `2dbbefa4b1d575ae9a14a4e8db3f03ad9303edb97cca2ba8e97afa06e61e89fb`.
Concept `jis_term_8a265222f4ab4cd0e9790206`, semantic concept
`jis_sem_df73e0f1e0c2e718a31e630a`.
Statement provenance for `euler_odd_perfect_form`: T. McCormack and J. Zelinsky,
*Weighted Versions of the Arithmetic-Mean-Geometric Mean Inequality and Zaremba's
Function*, arXiv:2312.11661v3, arXiv source archive SHA-256
`e3b37ff5b8d68c8411933361a4ee0d7395d98f386bb47b3ea1ba9b6fd34b67c1`,
decompressed `main.tex` SHA-256
`86b578e704fe4998f7f8013d41a6a7ebd174987e163c9008e5a65aa184d984a4`.
Around line 680 of `main.tex`, the paper states that
an odd perfect `n` has the form `n = q^s m^2` with `q` prime,
`q ≡ s ≡ 1 (mod 4)`, and `(q, m) = 1`. This is a statement source only; the Lean
proof below follows the standard route via multiplicativity of `σ`, parity of
geometric prime-power divisor sums, uniqueness of the single even factor (since
`2 * n ≡ 2 (mod 4)`), and collecting every other prime exponent into a square.
The statement is conditional and does not assert that an odd perfect number exists.
-/
/-! Auxiliary parity facts for the Euler-form proof below. These are local helpers
only; the public API of this module consists of `EulerianForm`, `IsEulerPrime`,
their projections, and `euler_odd_perfect_form`. Elementary parity steps reuse
Mathlib (`Odd.mul`, `Odd.pow`, `Even.add_odd`, `Odd.add_odd`, `Even.add_one`,
`Odd.add_one`, `Nat.not_even_iff_odd`, `odd_one`); only the facts below need
local proofs. -/
@[path]
private lemma prod_odd_of_all_odd {f : ℕ → ℕ} : ∀ (s : Finset ℕ),
  (∀ p ∈ s, Odd (f p)) → Odd (Finset.prod s f) := by
  intro s
  refine Finset.induction ?b ?st s
  · intro h
    simp only [Finset.prod_empty]
    exact odd_one
  · intro a t hat ih h
    have ha : Odd (f a) := h a (Finset.mem_insert_self a t)
    have ht : ∀ p ∈ t, Odd (f p) := fun p hp => h p (Finset.mem_insert_of_mem hp)
    have ihp := ih ht
    have hp : Finset.prod (insert a t) f = f a * Finset.prod t f :=
      Finset.prod_insert hat
    rw [hp]
    exact Odd.mul ha ihp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[geom_odd_iff_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
private lemma geom_odd_iff_even {p e : ℕ} (hp : Odd p) :
  Odd (Finset.sum (Finset.range (e + 1)) (fun i => p ^ i)) ↔ Even e := by
  induction e with
  | zero =>
    have hsum : Finset.sum (Finset.range (0 + 1)) (fun i => p ^ i) = 1 := by
      rw [Finset.sum_range_succ]; simp
    rw [hsum]
    constructor
    · intro _; exact ⟨0, rfl⟩
    · intro _; exact odd_one
  | succ e ih =>
    have hpow : Odd (p ^ (e + 1)) := Odd.pow hp
    have hsum_succ : Finset.sum (Finset.range (e + 1 + 1)) (fun i => p ^ i) =
      Finset.sum (Finset.range (e + 1)) (fun i => p ^ i) + p ^ (e + 1) := by
      rw [Finset.sum_range_succ]
    rw [hsum_succ]
    by_cases hS : Even (Finset.sum (Finset.range (e + 1)) (fun i => p ^ i))
    · have hOddSum : Odd (Finset.sum (Finset.range (e + 1)) (fun i => p ^ i) +
      p ^ (e + 1)) := Even.add_odd hS hpow
      have hNotOddS : ¬ Odd (Finset.sum (Finset.range (e + 1)) (fun i => p ^ i)) :=
        fun ho => Nat.not_even_iff_odd.mpr ho hS
      have hNotEvenE : ¬ Even e := fun he => hNotOddS (ih.mpr he)
      have hOddE : Odd e := Nat.not_even_iff_odd.mp hNotEvenE
      have hEvenSucc : Even (e + 1) := Odd.add_one hOddE
      constructor
      · intro _; exact hEvenSucc
      · intro _; exact hOddSum
    · have hOddS : Odd (Finset.sum (Finset.range (e + 1)) (fun i => p ^ i)) :=
      Nat.not_even_iff_odd.mp hS
      have hEvenE : Even e := ih.mp hOddS
      have hEvenSum : Even (Finset.sum (Finset.range (e + 1)) (fun i => p ^ i) +
        p ^ (e + 1)) := Odd.add_odd hOddS hpow
      have hNotOddSum : ¬ Odd (Finset.sum (Finset.range (e + 1)) (fun i => p ^ i) +
        p ^ (e + 1)) := fun ho => Nat.not_even_iff_odd.mpr ho hEvenSum
      have hOddSucc : Odd (e + 1) := Even.add_one hEvenE
      have hNotEvenSucc : ¬ Even (e + 1) := Nat.not_even_iff_odd.mpr hOddSucc
      constructor
      · intro ho; exact absurd ho hNotOddSum
      · intro he; exact absurd he hNotEvenSucc

end MetaMathlibExt

namespace MetaMathlibExt

/--
[EulerianForm_perfect](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma EulerianForm_perfect
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  Nat.Perfect N :=
-- proof
  h.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[EulerianForm_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma EulerianForm_odd
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  Odd N :=
-- proof
  h.2.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[EulerianForm_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma EulerianForm_prime
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  Nat.Prime q :=
-- proof
  h.2.2.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[EulerianForm_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma EulerianForm_eq
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  N = q ^ k * n ^ 2 :=
-- proof
  h.2.2.2.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[EulerianForm_mod4_q](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma EulerianForm_mod4_q
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  q % 4 = 1 :=
-- proof
  h.2.2.2.2.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[EulerianForm_mod4_k](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma EulerianForm_mod4_k
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  k % 4 = 1 :=
-- proof
  h.2.2.2.2.2.1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[EulerianForm_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma EulerianForm_coprime
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  Nat.Coprime q n :=
-- proof
  h.2.2.2.2.2.2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsEulerPrime_intro](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma IsEulerPrime_intro
  {N q k n : ℕ}
-- given
  (h : EulerianForm N q k n) :
-- imply
  IsEulerPrime N q :=
-- proof
  ⟨k, n, h⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsEulerPrime_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma IsEulerPrime_iff
  {N q : ℕ} :
-- imply
  IsEulerPrime N q ↔ ∃ k n, EulerianForm N q k n :=
-- proof
  Iff.rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsEulerPrime_perfect](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma IsEulerPrime_perfect
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  Nat.Perfect N := by
-- proof
  obtain ⟨k, n, hW⟩ := h
  exact EulerianForm_perfect hW

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsEulerPrime_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma IsEulerPrime_odd
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  Odd N := by
-- proof
  obtain ⟨k, n, hW⟩ := h
  exact EulerianForm_odd hW

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsEulerPrime_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma IsEulerPrime_prime
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  Nat.Prime q := by
-- proof
  obtain ⟨k, n, hW⟩ := h
  exact EulerianForm_prime hW

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsEulerPrime_factor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma IsEulerPrime_factor_eq
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  ∃ k n, N = q ^ k * n ^ 2 := by
-- proof
  obtain ⟨k, n, hW⟩ := h
  exact ⟨k, n, EulerianForm_eq hW⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsEulerPrime_exists_factor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma IsEulerPrime_exists_factor
  {N q : ℕ}
-- given
  (h : IsEulerPrime N q) :
-- imply
  ∃ k n, N = q ^ k * n ^ 2 ∧ q % 4 = 1 ∧ k % 4 = 1 ∧
    Nat.Coprime q n := by
-- proof
  obtain ⟨k, n, hW⟩ := h
  exact ⟨k, n, EulerianForm_eq hW, EulerianForm_mod4_q hW,
    EulerianForm_mod4_k hW, EulerianForm_coprime hW⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[euler_odd_perfect_form](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EulerPrime.lean)
-/
@[path]
lemma euler_odd_perfect_form
  {n : ℕ}
-- given
  (hodd : Odd n)
  (hperf : n.Perfect) :
-- imply
  ∃ q s m : ℕ,
    q.Prime ∧ n = q ^ s * m ^ 2 ∧ Nat.ModEq 4 q 1 ∧
    Nat.ModEq 4 s 1 ∧ q.Coprime m := by
-- proof
  have hpos : 0 < n := by have h2 := hperf.2; omega
  have hn0 : n ≠ 0 := by omega
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self _ hn0
  have hsum2 : Finset.sum n.divisors (fun d => d) = 2 * n :=
    (Nat.perfect_iff_sum_divisors_eq_two_mul hpos).mp hperf
  have h2n_mod4 : (2 * n) % 4 = 2 := by obtain ⟨k, hk⟩ := hodd; omega
  have hnot4dvd : ¬ 4 ∣ 2 * n := by intro hdiv; obtain ⟨t, ht⟩ := hdiv; omega
  have hsum_eq_prod : Finset.sum n.divisors (fun d => d) =
    Finset.prod n.primeFactors
      (fun p => Finset.sum (Finset.range (n.factorization p + 1))
        (fun i => p ^ i)) :=
    Nat.sum_divisors hn0
  have hprod_eq_2n : Finset.prod n.primeFactors
    (fun p => Finset.sum (Finset.range (n.factorization p + 1))
      (fun i => p ^ i)) =
    2 * n := by rw [← hsum_eq_prod, hsum2]
  have heven_2n : Even (2 * n) := ⟨n, by ring⟩
  have hprod_even : Even (Finset.prod n.primeFactors
    (fun p => Finset.sum (Finset.range (n.factorization p + 1))
      (fun i => p ^ i))) := by
    rw [hprod_eq_2n]; exact heven_2n
  have hprime_dvd : ∀ p ∈ n.primeFactors, p ∣ n := by
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).2.1
  have hprime_prime : ∀ p ∈ n.primeFactors, p.Prime := by
    intro p hp; exact (Nat.mem_primeFactors.mp hp).1
  have hprime_odd : ∀ p ∈ n.primeFactors, Odd p := by
    intro p hp
    have hp_dvd := hprime_dvd p hp
    apply Nat.not_even_iff_odd.mp
    intro heven_p
    obtain ⟨t, ht⟩ := hp_dvd
    have hev_mul : Even (p * t) := Even.mul_right heven_p t
    have hteq : p * t = n := ht.symm
    rw [hteq] at hev_mul
    exact Nat.not_even_iff_odd.mpr hodd hev_mul
  have hgeom : ∀ p ∈ n.primeFactors,
    Odd (Finset.sum (Finset.range (n.factorization p + 1)) (fun i => p ^ i)) ↔
      Even (n.factorization p) := by
    intro p hp
    have hp_odd := hprime_odd p hp
    exact geom_odd_iff_even hp_odd
  have hexists_even : ∃ q ∈ n.primeFactors,
    Even (Finset.sum (Finset.range (n.factorization q + 1))
      (fun i => q ^ i)) := by
    by_contra hcon
    have hall_odd : ∀ p ∈ n.primeFactors,
      Odd (Finset.sum (Finset.range (n.factorization p + 1))
        (fun i => p ^ i)) := by
      intro p hp
      apply Nat.not_even_iff_odd.mp
      intro he
      exact hcon ⟨p, hp, he⟩
    have hodd_prod := prod_odd_of_all_odd n.primeFactors hall_odd
    exact Nat.not_even_iff_odd.mpr hodd_prod hprod_even
  obtain ⟨q, hq_mem, hq_even⟩ := hexists_even
  have hq_prime : q.Prime := hprime_prime q hq_mem
  have huniq : ∀ p ∈ n.primeFactors,
    Even (Finset.sum (Finset.range (n.factorization p + 1))
      (fun i => p ^ i)) →
      p = q := by
    intro p hp heven_p
    by_contra hne
    have hp_ne_q : p ≠ q := hne
    have h_ins_q : insert q (n.primeFactors.erase q) = n.primeFactors :=
      Finset.insert_erase hq_mem
    have hnot_q : q ∉ n.primeFactors.erase q := by
      first | exact Finset.not_mem_erase q _ | simp
    have hprod_q : Finset.prod n.primeFactors
      (fun r => Finset.sum (Finset.range (n.factorization r + 1))
        (fun i => r ^ i)) =
      Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) *
        Finset.prod (n.primeFactors.erase q)
          (fun r => Finset.sum (Finset.range (n.factorization r + 1))
            (fun i => r ^ i)) := by
      conv_lhs => rw [← h_ins_q, Finset.prod_insert hnot_q]
    have hp_erase : p ∈ n.primeFactors.erase q :=
      Finset.mem_erase.mpr ⟨hp_ne_q, hp⟩
    have h_ins_p : insert p ((n.primeFactors.erase q).erase p) =
      n.primeFactors.erase q := Finset.insert_erase hp_erase
    have hnot_p : p ∉ (n.primeFactors.erase q).erase p := by
      first | exact Finset.not_mem_erase p _ | simp
    have hprod_p : Finset.prod (n.primeFactors.erase q)
      (fun r => Finset.sum (Finset.range (n.factorization r + 1))
        (fun i => r ^ i)) =
      Finset.sum (Finset.range (n.factorization p + 1)) (fun i => p ^ i) *
        Finset.prod ((n.primeFactors.erase q).erase p)
          (fun r => Finset.sum (Finset.range (n.factorization r + 1))
            (fun i => r ^ i)) := by
      conv_lhs => rw [← h_ins_p, Finset.prod_insert hnot_p]
    have hprod_eq : Finset.prod n.primeFactors
      (fun r => Finset.sum (Finset.range (n.factorization r + 1))
        (fun i => r ^ i)) =
      Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) *
        (Finset.sum (Finset.range (n.factorization p + 1)) (fun i => p ^ i) *
          Finset.prod ((n.primeFactors.erase q).erase p)
            (fun r => Finset.sum (Finset.range (n.factorization r + 1))
              (fun i => r ^ i))) := by rw [hprod_q, hprod_p]
    obtain ⟨a, ha⟩ := heven_p
    obtain ⟨b, hb⟩ := hq_even
    have h4dvd : 4 ∣ Finset.prod n.primeFactors
      (fun r => Finset.sum (Finset.range (n.factorization r + 1))
        (fun i => r ^ i)) :=
      ⟨b * (a * Finset.prod ((n.primeFactors.erase q).erase p)
        (fun r => Finset.sum (Finset.range (n.factorization r + 1))
          (fun i => r ^ i))),
        by rw [hprod_eq, ha, hb]; ring⟩
    rw [hprod_eq_2n] at h4dvd
    exact hnot4dvd h4dvd
  have hodd_ne : ∀ p ∈ n.primeFactors, p ≠ q →
    Odd (Finset.sum (Finset.range (n.factorization p + 1))
      (fun i => p ^ i)) := by
    intro p hp hne
    apply Nat.not_even_iff_odd.mp
    intro he
    exact hne (huniq p hp he)
  have heven_exp_ne : ∀ p ∈ n.primeFactors, p ≠ q →
    Even (n.factorization p) := by
    intro p hp hne
    exact ((hgeom p hp).mp (hodd_ne p hp hne))
  have hodd_exp_q : Odd (n.factorization q) := by
    have hNotOdd : ¬ Odd
      (Finset.sum (Finset.range (n.factorization q + 1))
        (fun i => q ^ i)) :=
      fun ho => Nat.not_even_iff_odd.mpr ho hq_even
    have hNotEven : ¬ Even (n.factorization q) :=
      fun he => hNotOdd ((hgeom q hq_mem).mpr he)
    exact Nat.not_even_iff_odd.mp hNotEven
  have hfact : n = Finset.prod n.primeFactors (fun p => p ^ n.factorization p) :=
    Nat.prod_primeFactors_pow_factorization hn0
  have hsplit : Finset.prod n.primeFactors (fun p => p ^ n.factorization p) =
    q ^ n.factorization q *
      Finset.prod (n.primeFactors.erase q)
        (fun p => p ^ n.factorization p) := by
    have h_ins : insert q (n.primeFactors.erase q) = n.primeFactors :=
      Finset.insert_erase hq_mem
    have hnot : q ∉ n.primeFactors.erase q := by
      first | exact Finset.not_mem_erase q _ | simp
    conv_lhs => rw [← h_ins, Finset.prod_insert hnot]
  have hm2 : (Finset.prod (n.primeFactors.erase q)
    (fun p => p ^ (n.factorization p / 2))) ^ 2 =
    Finset.prod (n.primeFactors.erase q)
      (fun p => p ^ n.factorization p) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro p hp
    have hmem := Finset.mem_erase.mp hp
    have heven_e : Even (n.factorization p) := heven_exp_ne p hmem.2 hmem.1
    obtain ⟨r, hr⟩ := heven_e
    have hdiv := Nat.div_add_mod (n.factorization p) 2
    have hdiv2 : (n.factorization p / 2) * 2 = n.factorization p := by omega
    rw [← pow_mul, hdiv2]
  have hn_eq : n = q ^ n.factorization q *
    (Finset.prod (n.primeFactors.erase q)
      (fun p => p ^ (n.factorization p / 2))) ^ 2 := by
    conv_lhs => rw [hfact, hsplit]
    rw [hm2]
  have hAq_even : Even
    (Finset.sum (Finset.range (n.factorization q + 1))
      (fun i => q ^ i)) := hq_even
  have hA_mod : (Finset.sum (Finset.range (n.factorization q + 1))
    (fun i => q ^ i)) % 4 = 2 := by
    have hAE := hAq_even
    obtain ⟨r, hr⟩ := hAE
    have h04 : Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) % 4 = 0 ∨
      Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) % 4 = 1 ∨
      Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) % 4 = 2 ∨
      Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) % 4 = 3 := by
      omega
    have h02 : Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) % 4 = 0 ∨
      Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) % 4 = 2 := by
      omega
    cases h02 with
    | inl h0 =>
      have hdiv := Nat.div_add_mod
        (Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i)) 4
      have hA4 : Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) =
        4 * (Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) / 4) := by
        omega
      have hprod4 : (Finset.prod n.primeFactors
        (fun p => Finset.sum (Finset.range (n.factorization p + 1))
          (fun i => p ^ i))) % 4 = 0 := by
        have h_ins : insert q (n.primeFactors.erase q) = n.primeFactors :=
          Finset.insert_erase hq_mem
        have hnot : q ∉ n.primeFactors.erase q := by
          first | exact Finset.not_mem_erase q _ | simp
        have hpe : Finset.prod n.primeFactors
          (fun p => Finset.sum (Finset.range (n.factorization p + 1))
            (fun i => p ^ i)) =
          Finset.sum (Finset.range (n.factorization q + 1)) (fun i => q ^ i) *
            Finset.prod (n.primeFactors.erase q)
              (fun p => Finset.sum (Finset.range (n.factorization p + 1))
                (fun i => p ^ i)) := by
          conv_lhs => rw [← h_ins, Finset.prod_insert hnot]
        rw [hpe, hA4]
        have hmm : (4 * (Finset.sum (Finset.range (n.factorization q + 1))
          (fun i => q ^ i) / 4) *
          Finset.prod (n.primeFactors.erase q)
            (fun p => Finset.sum (Finset.range (n.factorization p + 1))
              (fun i => p ^ i))) =
          4 * ((Finset.sum (Finset.range (n.factorization q + 1))
            (fun i => q ^ i) / 4) *
            Finset.prod (n.primeFactors.erase q)
              (fun p => Finset.sum (Finset.range (n.factorization p + 1))
                (fun i => p ^ i))) := by ring
        rw [hmm]
        omega
      rw [hprod_eq_2n] at hprod4
      omega
    | inr h2 => exact h2
  have hq_odd := hprime_odd q hq_mem
  have hq13 : q % 4 = 1 ∨ q % 4 = 3 := by obtain ⟨k, hk⟩ := hq_odd; omega
  have hq1 : q % 4 = 1 := by
    by_contra hcon
    have hq3 : q % 4 = 3 := by omega
    obtain ⟨t, ht⟩ := hodd_exp_q
    have hdiv1 := Nat.div_add_mod (1 + q) 4
    have h1q0 : (1 + q) % 4 = 0 := by omega
    have h1q4 : 1 + q = 4 * ((1 + q) / 4) := by omega
    have hpair : ∀ k : ℕ, 4 ∣ (q ^ (2 * k) + q ^ (2 * k + 1)) := by
      intro k
      have hqp : q ^ (2 * k) + q ^ (2 * k + 1) = q ^ (2 * k) * (1 + q) := by
        have hp1 : q ^ (2 * k + 1) = q ^ (2 * k) * q := pow_succ q (2 * k)
        rw [hp1]
        ring
      refine ⟨q ^ (2 * k) * ((1 + q) / 4), ?_⟩
      rw [hqp]
      nth_rewrite 1 [h1q4]
      ring
    have hsum4 : 4 ∣ Finset.sum (Finset.range (n.factorization q + 1))
      (fun i => q ^ i) := by
      have hst : n.factorization q + 1 = 2 * (t + 1) := by omega
      have hpair_sum : ∀ u : ℕ, Finset.sum (Finset.range (2 * u))
        (fun i => q ^ i) = Finset.sum (Finset.range u)
          (fun k => (q ^ (2 * k) + q ^ (2 * k + 1))) := by
        intro u
        induction u with
        | zero => simp
        | succ v ih =>
          have e1 : 2 * (v + 1) = 2 * v + 2 := by ring
          have e2 : Finset.sum (Finset.range (2 * v + 2)) (fun i => q ^ i) =
            Finset.sum (Finset.range (2 * v)) (fun i => q ^ i) +
              (q ^ (2 * v) + q ^ (2 * v + 1)) := by
            rw [show 2 * v + 2 = (2 * v + 1) + 1 from by omega,
              Finset.sum_range_succ,
              show 2 * v + 1 = (2 * v) + 1 from by omega,
              Finset.sum_range_succ]; ring
          have e3 : Finset.sum (Finset.range (v + 1))
            (fun k => (q ^ (2 * k) + q ^ (2 * k + 1))) =
            Finset.sum (Finset.range v)
              (fun k => (q ^ (2 * k) + q ^ (2 * k + 1))) +
              (q ^ (2 * v) + q ^ (2 * v + 1)) := by
            rw [Finset.sum_range_succ]
          rw [e1, e2, e3, ih]
      have h4u : ∀ u : ℕ, 4 ∣ Finset.sum (Finset.range u)
        (fun k => (q ^ (2 * k) + q ^ (2 * k + 1))) := by
        intro u
        induction u with
        | zero => simp
        | succ v ih2 =>
          rw [Finset.sum_range_succ]
          obtain ⟨a, ha⟩ := ih2
          obtain ⟨b, hb⟩ := hpair v
          exact ⟨a + b, by rw [ha, hb]; ring⟩
      rw [hst]
      rw [hpair_sum (t + 1)]
      exact h4u (t + 1)
    obtain ⟨c, hc⟩ := hsum4
    omega
  have hqMod : Nat.ModEq 4 q 1 := by unfold Nat.ModEq; simp [hq1]
  have hqW : ∃ k, q = 4 * k + 1 := ⟨q / 4, by
    have hdiv := Nat.div_add_mod q 4; omega⟩
  obtain ⟨qk, hqk⟩ := hqW
  have hpow41 : ∀ i : ℕ, ∃ ti, q ^ i = 4 * ti + 1 := by
    intro i
    induction i with
    | zero => exact ⟨0, by simp⟩
    | succ j ih2 =>
      obtain ⟨tj, htj⟩ := ih2
      have hs : q ^ (j + 1) = (q ^ j) * q := by rw [pow_succ]
      exact ⟨4 * tj * qk + tj + qk, by rw [hs, htj, hqk]; ring⟩
  have hS41 : ∃ T, Finset.sum (Finset.range (n.factorization q + 1))
    (fun i => q ^ i) = 4 * T + (n.factorization q + 1) := by
    induction n.factorization q with
    | zero => exact ⟨0, by rw [Finset.sum_range_succ]; simp⟩
    | succ e ih2 =>
      obtain ⟨T0, hT0⟩ := ih2
      obtain ⟨te, hte⟩ := hpow41 (e + 1)
      have hs : Finset.sum (Finset.range (e + 1 + 1)) (fun i => q ^ i) =
        Finset.sum (Finset.range (e + 1)) (fun i => q ^ i) + q ^ (e + 1) := by
        rw [Finset.sum_range_succ]
      exact ⟨T0 + te, by rw [hs, hT0, hte]; ring⟩
  have hs1 : n.factorization q % 4 = 1 := by
    obtain ⟨T, hT⟩ := hS41
    omega
  have hsMod : Nat.ModEq 4 (n.factorization q) 1 := by
    unfold Nat.ModEq; simp [hs1]
  have hm_ne : Finset.prod (n.primeFactors.erase q)
    (fun p => p ^ (n.factorization p / 2)) ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by norm_num), mul_zero] at hn_eq
    exact hn0 hn_eq
  have hm_pos : 0 < Finset.prod (n.primeFactors.erase q)
    (fun p => p ^ (n.factorization p / 2)) := by omega
  have hnotdvd : ¬ q ∣ Finset.prod (n.primeFactors.erase q)
    (fun p => p ^ (n.factorization p / 2)) := by
    intro hdiv
    obtain ⟨p, hpm, hpd⟩ :=
      (hq_prime.prime.dvd_finsetProd_iff
        (fun p => p ^ (n.factorization p / 2))).mp hdiv
    have hmem := Finset.mem_erase.mp hpm
    have hp_prime := hprime_prime p hmem.2
    have heq : q = p := Nat.prime_eq_prime_of_dvd_pow hq_prime hp_prime hpd
    exact hmem.1 heq.symm
  have hcop : q.Coprime (Finset.prod (n.primeFactors.erase q)
    (fun p => p ^ (n.factorization p / 2))) :=
    (Nat.Prime.coprime_iff_not_dvd hq_prime).mpr hnotdvd
  exact ⟨q, n.factorization q, Finset.prod (n.primeFactors.erase q)
    (fun p => p ^ (n.factorization p / 2)), hq_prime, hn_eq, hqMod, hsMod, hcop⟩

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-28

import Mathlib
import Initialize.Tactic.Attr.Basic
open Finset


namespace MetaMathlibExt

/--
[bonse_primes_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
lemma bonse_primes_infinite
  :
-- imply
  (Set.ofPred fun p : ℕ => Prime p).Infinite := by
-- proof
  have h := Nat.infinite_setOfPred_prime
  have heq : Set.ofPred (fun p : ℕ => Prime p) = Set.ofPred Nat.Prime := by
    ext x
    exact Nat.prime_iff.symm
  rwa [heq]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bonse_nth_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
lemma bonse_nth_strictMono
  :
-- imply
  StrictMono (Nat.nth Prime) :=
-- proof
  Nat.nth_strictMono bonse_primes_infinite

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bonse_nth_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
lemma bonse_nth_prime
  (k : ℕ) :
-- imply
  Prime (Nat.nth Prime k) :=
-- proof
  Nat.nth_mem_of_infinite bonse_primes_infinite k

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bonse_nth_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
lemma bonse_nth_five
  :
-- imply
  Nat.nth Prime 5 = 13 := by
-- proof
  have c13 : Nat.count Prime 13 = 5 := by decide
  have h13 : Prime 13 := by decide
  have h := Nat.nth_count h13
  rwa [c13] at h

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bonse_nth_succ_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
lemma bonse_nth_succ_lt
  (k : ℕ) :
-- imply
  Nat.nth Prime (k + 1) < 2 * Nat.nth Prime k := by
-- proof
  have hne0 : Nat.nth Prime k ≠ 0 := by
    have h2 := (Nat.prime_iff.mpr (bonse_nth_prime k)).two_le
    omega
  obtain ⟨p, hpNat, hlt, hle⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (Nat.nth Prime k) hne0
  have hp : Prime p := Nat.prime_iff.mp hpNat
  have hcount : k + 1 ≤ Nat.count Prime p := by
    by_contra h
    have hle' : Nat.count Prime p ≤ k := by omega
    have hmono := bonse_nth_strictMono.monotone hle'
    rw [Nat.nth_count hp] at hmono
    omega
  have hle_nth : Nat.nth Prime (k + 1) ≤ p :=
    le_trans (bonse_nth_strictMono.monotone hcount) (le_of_eq (Nat.nth_count hp))
  have hne : p ≠ 2 * Nat.nth Prime k := by
    intro h
    have hdvd : Nat.nth Prime k ∣ p := ⟨2, by omega⟩
    obtain h1 | hpk := hpNat.eq_one_or_self_of_dvd (Nat.nth Prime k) hdvd
    · have h2 := (Nat.prime_iff.mpr (bonse_nth_prime k)).two_le
      omega
    · omega
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bonse_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BonseInequality.lean)
-/
@[path]
lemma bonse_inequality
  {k : ℕ}
-- given
  (hk : 4 < k) :
-- imply
  (Nat.nth Prime k) ^ 2 < ∏ i ∈ Finset.range k, Nat.nth Prime i := by
-- proof
  have key : ∀ m : ℕ, 5 ≤ m →
    (Nat.nth Prime m) ^ 2 < ∏ i ∈ Finset.range m, Nat.nth Prime i := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      have c2 : Nat.count Prime 2 = 0 := by decide
      have c3 : Nat.count Prime 3 = 1 := by decide
      have c5 : Nat.count Prime 5 = 2 := by decide
      have c7 : Nat.count Prime 7 = 3 := by decide
      have c11 : Nat.count Prime 11 = 4 := by decide
      have c13 : Nat.count Prime 13 = 5 := by decide
      have n0 : Nat.nth Prime 0 = 2 := by
        have h2 : Prime 2 := by decide
        have h := Nat.nth_count h2
        rwa [c2] at h
      have n1 : Nat.nth Prime 1 = 3 := by
        have h3 : Prime 3 := by decide
        have h := Nat.nth_count h3
        rwa [c3] at h
      have n2 : Nat.nth Prime 2 = 5 := by
        have h5 : Prime 5 := by decide
        have h := Nat.nth_count h5
        rwa [c5] at h
      have n3 : Nat.nth Prime 3 = 7 := by
        have h7 : Prime 7 := by decide
        have h := Nat.nth_count h7
        rwa [c7] at h
      have n4 : Nat.nth Prime 4 = 11 := by
        have h11 : Prime 11 := by decide
        have h := Nat.nth_count h11
        rwa [c11] at h
      have n5 : Nat.nth Prime 5 = 13 := by
        have h13 : Prime 13 := by decide
        have h := Nat.nth_count h13
        rwa [c13] at h
      simp only [Finset.prod_range_succ, n0, n1, n2, n3, n4, n5]
      norm_num
    | succ n hn ih =>
      have hB := bonse_nth_succ_lt n
      have h4 : 4 ≤ Nat.nth Prime n := by
        have hmono := bonse_nth_strictMono.monotone hn
        rw [bonse_nth_five] at hmono
        omega
      have hpos : 0 < Nat.nth Prime n := by omega
      have hsq : (Nat.nth Prime (n + 1)) ^ 2 < 4 * (Nat.nth Prime n) ^ 2 := by
        nlinarith [hB, hpos]
      have hmul : 4 * (Nat.nth Prime n) ^ 2 ≤
        Nat.nth Prime n * (Nat.nth Prime n) ^ 2 :=
        Nat.mul_le_mul h4 le_rfl
      have hlt : Nat.nth Prime n * (Nat.nth Prime n) ^ 2 <
        Nat.nth Prime n * ∏ i ∈ Finset.range n, Nat.nth Prime i :=
        mul_lt_mul_of_pos_left ih hpos
      have hprod : ∏ i ∈ Finset.range (n + 1), Nat.nth Prime i =
        Nat.nth Prime n * ∏ i ∈ Finset.range n, Nat.nth Prime i := by
        rw [Finset.prod_range_succ, mul_comm]
      calc (Nat.nth Prime (n + 1)) ^ 2
        < 4 * (Nat.nth Prime n) ^ 2 := hsq
        _ ≤ Nat.nth Prime n * (Nat.nth Prime n) ^ 2 := hmul
        _ < Nat.nth Prime n * ∏ i ∈ Finset.range n, Nat.nth Prime i := hlt
        _ = ∏ i ∈ Finset.range (n + 1), Nat.nth Prime i := hprod.symm
  exact key k (by omega)

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26

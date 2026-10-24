import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.KFull
open Nat


namespace Nat

/--
[powerfulPart_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma powerfulPart_factorization
  {n p : ℕ} :
-- imply
  (powerfulPart n).factorization p =
    if 2 ≤ n.factorization p then n.factorization p else 0 := by
-- proof
  unfold powerfulPart
  rw [Nat.factorization_prod_apply (fun q hq =>
    pow_ne_zero _ (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq)).ne_zero)]
  have hterm : ∀ q : ℕ, q ∈ n.primeFactors.filter (fun q => 2 ≤ n.factorization q) →
    (q ^ n.factorization q).factorization p =
      if q = p then n.factorization q else 0 := by
    intro q hq
    have hqprime : q.Prime :=
      Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter q hq)
    by_cases hqp : q = p
    · subst hqp
      rw [if_pos rfl, Nat.factorization_pow_self hqprime]
    · rw [if_neg hqp, Nat.factorization_pow, Finsupp.smul_apply,
      hqprime.factorization, Finsupp.single_apply, if_neg hqp,
      smul_eq_mul, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  by_cases hp2 : 2 ≤ n.factorization p
  · rw [if_pos hp2]
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hp2
    have hprime : p.Prime := by
      by_contra hnp
      have h0 := Nat.factorization_eq_zero_of_not_prime n hnp
      omega
    have hdvd : p ∣ n := by
      by_contra hnd
      have h0 := Nat.factorization_eq_zero_of_not_dvd hnd
      omega
    have hpmem : p ∈ n.primeFactors.filter (fun q => 2 ≤ n.factorization q) := by
      rw [Finset.mem_filter]
      exact ⟨Nat.mem_primeFactors.mpr ⟨hprime, hdvd, hn0⟩, hp2⟩
    rw [if_pos hpmem]
  · rw [if_neg hp2]
    have hnotmem : p ∉ n.primeFactors.filter (fun q => 2 ≤ n.factorization q) :=
      fun h => hp2 (Finset.mem_filter.mp h).2
    rw [if_neg hnotmem]

end Nat

namespace Nat

/--
[powerfulPart_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma powerfulPart_dvd
  {n : ℕ} :
-- imply
  powerfulPart n ∣ n := by
-- proof
  obtain rfl | hn := eq_or_ne n 0
  · rw [powerfulPart_zero]
    exact one_dvd 0
  · have hpos : powerfulPart n ≠ 0 := by
    unfold powerfulPart
    exact Finset.prod_ne_zero_iff.mpr fun q hq =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors
        (Finset.mem_of_mem_filter q hq)).ne_zero
    rw [← Nat.factorization_le_iff_dvd hpos hn]
    intro q
    rw [powerfulPart_factorization]
    split_ifs with h
    · exact le_rfl
    · exact zero_le _

end Nat

namespace Nat

/--
[isKFull_iff_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma isKFull_iff_factorization
  {k n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  IsKFull k n ↔ ∀ p : ℕ, p.Prime → p ∣ n → k ≤ n.factorization p := by
-- proof
  constructor
  · intro h p hp hpn
    exact (hp.pow_dvd_iff_le_factorization hn).mp (h.2 p hp hpn)
  · intro h
    exact ⟨hn, fun p hp hpn => (hp.pow_dvd_iff_le_factorization hn).mpr (h p hp hpn)⟩

end Nat

namespace Nat

/--
[not_isKFull_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma not_isKFull_zero
  {k : ℕ} :
-- imply
  ¬ IsKFull k 0 :=
-- proof
  fun h => h.1 rfl

end Nat

namespace Nat

/--
[isKFull_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma isKFull_one
  {k : ℕ} :
-- imply
  IsKFull k 1 :=
-- proof
  ⟨one_ne_zero, fun _p hp hpn => absurd (Nat.dvd_one.mp hpn) hp.ne_one⟩

end Nat

namespace Nat

/--
[isKFull_k_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma isKFull_k_eq_zero
  {n : ℕ} :
-- imply
  IsKFull 0 n ↔ n ≠ 0 := by
-- proof
  constructor
  · exact fun h => h.1
  · intro hn
    refine ⟨hn, fun p _ _ => ?_⟩
    rw [pow_zero]
    exact one_dvd n

end Nat

namespace Nat

/--
[isKFull_k_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma isKFull_k_eq_one
  {n : ℕ} :
-- imply
  IsKFull 1 n ↔ n ≠ 0 := by
-- proof
  constructor
  · exact fun h => h.1
  · intro hn
    exact ⟨hn, fun _ _ hpn => by simpa using hpn⟩

end Nat

namespace Nat

/--
[isKFull_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma isKFull_mono
  {j k n : ℕ}
-- given
  (hjk : j ≤ k)
  (h : IsKFull k n) :
-- imply
  IsKFull j n :=
-- proof
  ⟨h.1, fun p hp hpn => (pow_dvd_pow p hjk).trans (h.2 p hp hpn)⟩

end Nat

namespace Nat

/--
[isKFull_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma isKFull_of_two_le
  {k n : ℕ}
-- given
  (hk : 2 ≤ k)
  (h : IsKFull k n) :
-- imply
  IsKFull 2 n :=
-- proof
  isKFull_mono hk h

end Nat

namespace Nat

/--
[isKFull_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
lemma isKFull_two
  {n : ℕ} :
-- imply
  IsKFull 2 n ↔ n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n :=
-- proof
  Iff.rfl

end Nat

/--
[powerfulPart_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma powerfulPart_zero_eq
  :
-- imply
  powerfulPart 0 = 1 := by
-- proof
  apply Nat.powerfulPart_zero

/--
[powerfulPart_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/KFull.lean)
-/
@[path]
private lemma powerfulPart_one_eq
  :
-- imply
  powerfulPart 1 = 1 := by
-- proof
  apply Nat.powerfulPart_one


-- created on 2026-10-20
-- updated on 2026-10-23

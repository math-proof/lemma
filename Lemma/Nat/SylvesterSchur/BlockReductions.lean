import Mathlib
import sympy.Basic
open Nat Nat.SylvesterSchur
open Finset Nat


namespace Nat.SylvesterSchur.Internal

/--
[bertrand_base](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma bertrand_base
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ n + 1 + i := by
-- proof
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ :=
    Nat.exists_prime_lt_and_le_two_mul n (Nat.pos_iff_ne_zero.mp (by omega))
  refine ⟨p - (n + 1), ?_, p, hp_prime, hp_gt, ?_⟩
  · omega
  · rw [Nat.add_sub_cancel' (by omega : n + 1 ≤ p)]

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[prime_dvd_seq_implies_choose](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma prime_dvd_seq_implies_choose
  {n k r : ℕ}
  {j : ℕ}
-- given
  (hr : r.Prime)
  (hr_gt : n < r)
  (hj : j < n)
  (hdvd : r ∣ k + j) :
-- imply
  r ∣ Nat.choose (k + n - 1) n :=
-- proof
  prime_dvd_choose_of_dvd_consecutive hr hr_gt hj hdvd

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[prime_dvd_choose_of_mem_interval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma prime_dvd_choose_of_mem_interval
  {n k p : ℕ}
-- given
  (hp : p.Prime)
  (hp_gt : n < p)
  (hp_ge : k ≤ p)
  (hp_le : p ≤ k + n - 1) :
-- imply
  p ∣ Nat.choose (k + n - 1) n :=
-- proof
  hp.dvd_choose hp_gt (by omega) hp_le

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_large_prime_dvd_term](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
private lemma exists_prime_dvd_choose_of_large_prime_dvd_term {n k i p : ℕ}
  (hi : i < n) (hp : p.Prime) (hp_gt : n < p) (hp_dvd : p ∣ k + i) :
  ∃ q : ℕ, q.Prime ∧ n < q ∧ q ∣ Nat.choose (k + n - 1) n :=
⟨p, hp, hp_gt, prime_dvd_seq_implies_choose hp hp_gt i hi hp_dvd⟩

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_large_prime_dvd_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_large_prime_dvd_block
  {n k : ℕ}
-- given
  (hblock : ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i) :
-- imply
  ∃ q : ℕ, q.Prime ∧ n < q ∧ q ∣ Nat.choose (k + n - 1) n := by
-- proof
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ := hblock
  exact exists_prime_dvd_choose_of_large_prime_dvd_term hi hp hp_gt hp_dvd

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[block_term_prime_factors_le_of_no_large_prime_dvd_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
private lemma block_term_prime_factors_le_of_no_large_prime_dvd_block {n k : ℕ}
  (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i)
  {i p : ℕ} (hi : i < n) (hp : p.Prime) (hp_dvd : p ∣ k + i) :
  p ≤ n := by
  by_contra hp_le
  push Not at hp_le
  exact hblock ⟨i, hi, p, hp, by omega, hp_dvd⟩

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[block_term_mem_smoothNumbers_succ_of_no_large_prime_dvd_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
private lemma block_term_mem_smoothNumbers_succ_of_no_large_prime_dvd_block {n k i : ℕ}
  (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i)
  (hi : i < n) :
  k + i ∈ Nat.smoothNumbers (n + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hp_dvd
  have hp_le :
    p ≤ n :=
    block_term_prime_factors_le_of_no_large_prime_dvd_block hblock hi hp hp_dvd
  omega

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[block_length_le_smoothNumbersUpTo_card_of_no_large_prime_dvd_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
private lemma block_length_le_smoothNumbersUpTo_card_of_no_large_prime_dvd_block
  {n k : ℕ}
  (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i) :
  n ≤ (Nat.smoothNumbersUpTo (k + n - 1) (n + 1)).card := by
  apply Finset.le_card_of_inj_on_range (fun i => k + i)
  · intro i hi
    rw [Nat.mem_smoothNumbersUpTo]
    have hle_top : k + i ≤ k + n - 1 := by
      calc
        k + i ≤ k + (n - 1) := Nat.add_le_add_left (Nat.le_sub_one_of_lt hi) k
        _ = k + n - 1 := by omega
    exact ⟨hle_top, block_term_mem_smoothNumbers_succ_of_no_large_prime_dvd_block hblock hi⟩
  · intro a _ha b _hb hab
    exact Nat.add_left_cancel hab

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[block_length_le_smoothNumbersUpTo_bound_of_no_large_prime_dvd_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
private lemma block_length_le_smoothNumbersUpTo_bound_of_no_large_prime_dvd_block
  {n k : ℕ}
  (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i) :
  n ≤ 2 ^ Nat.primeCounting n * Nat.sqrt (k + n - 1) := by
  have h :=
    (block_length_le_smoothNumbersUpTo_card_of_no_large_prime_dvd_block hblock).trans
    (Nat.smoothNumbersUpTo_card_le (k + n - 1) (n + 1))
  rwa [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting' (n + 1)]

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_dvd_block_or_dvd_recent_pred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
private lemma exists_dvd_block_or_dvd_recent_pred {n k p : ℕ} (hn : 0 < n) (hp_gt : n < p) :
  (∃ i < n, p ∣ k + i) ∨
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ p - n ∧ p ∣ k - j := by
  have hp_pos : 0 < p := by omega
  by_cases hmod0 : k % p = 0
  · left
    exact ⟨0, hn, by
      rw [Nat.dvd_iff_mod_eq_zero]
      simp [hmod0]⟩
  · let r := k % p
    have hr_lt : r < p := Nat.mod_lt k hp_pos
    have hr_pos : 0 < r := Nat.pos_of_ne_zero hmod0
    by_cases hhit : p - r < n
    · left
      refine ⟨p - r, hhit, ?_⟩
      have hsum_mod : k + (p - r) ≡ r + (p - r) [MOD p] :=
        (Nat.mod_modEq k p).symm.add_right (p - r)
      have hsum_eq : r + (p - r) = p := by omega
      exact Nat.modEq_zero_iff_dvd.mp <| hsum_mod.trans <| by
        simp [hsum_eq]
    · right
      have hr_le_pred : r ≤ p - n := by omega
      have hr_le_k : r ≤ k := Nat.mod_le k p
      refine ⟨r, by omega, hr_le_pred, ?_⟩
      have hmodEq : r ≡ k [MOD p] := by
        simpa [r] using Nat.mod_modEq k p
      exact (Nat.modEq_iff_dvd' hr_le_k).mp hmodEq

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_dvd_block_of_succ_succ_prime_not_dvd_pred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_dvd_block_of_succ_succ_prime_not_dvd_pred
  {n k s : ℕ}
-- given
  (hn : 0 < n)
  (hsn : s = n + 2)
  (hnot_one : ¬ s ∣ k - 1)
  (hnot_two : ¬ s ∣ k - 2) :
-- imply
  ∃ i < n, s ∣ k + i := by
-- proof
  rcases exists_dvd_block_or_dvd_recent_pred (n := n) (k := k) (p := s) hn (by omega)
    with hblock | hpred
  · exact hblock
  obtain ⟨j, hj1, hjle, hjdvd⟩ := hpred
  obtain rfl | rfl := (by omega : j = 1 ∨ j = 2)
  · exact (hnot_one hjdvd).elim
  · exact (hnot_two hjdvd).elim

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_large_start](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_large_start
  {n k : ℕ}
-- given
  (hn : 2 ≤ n)
  (hk : n < k)
  (hlarge : n ! * 2 ^ (n - 1) < k) :
-- imply
  ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
-- proof
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ := consecutive_of_large_start hn hk hlarge
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_half_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_half_bound
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * (k + n - 1) ^ (n / 2 + 1) < k ^ n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
-- proof
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_top_pow_half_add_one_lt_start_pow hn hk hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[start_le_quadratic_of_no_large_prime_dvd_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma start_le_quadratic_of_no_large_prime_dvd_block
  {n k : ℕ}
-- given
  (hn : 38 ≤ n)
  (hblock : ¬ ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i) :
-- imply
  k ≤ n ^ 2 := by
-- proof
  by_contra hkquad
  push Not at hkquad
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ := consecutive_of_quadratic_start hn hkquad
  exact hblock ⟨i, hi, p, hp, by omega, hp_dvd⟩

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_primeCounting_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_primeCounting_bound
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * (k + n - 1) ^ Nat.primeCounting n < k ^ n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
-- proof
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_top_pow_primeCounting_lt_start_pow hn hk hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_sqrt_primorial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_sqrt_primorial_bound
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * ((k + n - 1) ^ (Nat.sqrt (k + n - 1) + 1) * primorial n) < k ^ n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
-- proof
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_top_pow_sqrt_mul_primorial_lt_start_pow hn hk hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_erdos_layers_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_erdos_layers_bound
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)), if j = 0 then primorial n else primorial (Nat.nthRoot (j + 1) (k + n - 1))) < k ^ n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
-- proof
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_prod_erdos_layers_lt_start_pow hn hk hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_erdos_div_three_layers_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_erdos_div_three_layers_bound
  {n k : ℕ}
-- given
  (hk : n < k)
  (hN6 : 6 ≤ k + n - 1)
  (hbound : n ! * (∏ j ∈ Finset.range (Nat.log 2 (k + n - 1)), if j = 0 then primorial ((k + n - 1) / 3) else primorial (Nat.nthRoot (j + 1) (k + n - 1))) < k ^ n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
-- proof
  obtain ⟨i, hi, p, hp, hp_gt, hp_dvd⟩ :=
    consecutive_of_factorial_mul_prod_erdos_div_three_layers_lt_start_pow hk hN6 hbound
  exact ⟨p, hp, by omega, prime_dvd_seq_implies_choose hp (by omega) i hi hp_dvd⟩

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_erdos_layers_four_pow_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_erdos_layers_four_pow_bound
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * 4 ^ (n + Nat.sqrt (k + n - 1) * Nat.log 2 (k + n - 1)) < k ^ n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
-- proof
  apply exists_prime_dvd_choose_of_erdos_layers_bound hn hk
  have hprod := erdos_layers_le_four_pow (k + n - 1) n
  exact (Nat.mul_le_mul_left (n !) hprod).trans_lt hbound

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_erdos_layers_three_layers_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_erdos_layers_three_layers_bound
  {n k : ℕ}
-- given
  (hn : 1 ≤ n)
  (hk : n < k)
  (hbound : n ! * 4 ^ (n + Nat.sqrt (k + n - 1) + Nat.nthRoot 3 (k + n - 1) * Nat.log 2 (k + n - 1)) < k ^ n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
-- proof
  apply exists_prime_dvd_choose_of_erdos_layers_bound hn hk
  have hprod := erdos_layers_le_four_pow_three_layers (k + n - 1) n
  exact (Nat.mul_le_mul_left (n !) hprod).trans_lt hbound

end Nat.SylvesterSchur.Internal

namespace Nat.SylvesterSchur.Internal

/--
[exists_prime_dvd_choose_of_smooth_count_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/BlockReductions.lean)
-/
@[path]
lemma exists_prime_dvd_choose_of_smooth_count_bound
  {n k : ℕ}
-- given
  (hbound : 2 ^ Nat.primeCounting n * Nat.sqrt (k + n - 1) < n) :
-- imply
  ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ Nat.choose (k + n - 1) n := by
-- proof
  by_cases hblock : ∃ i < n, ∃ p : ℕ, p.Prime ∧ n < p ∧ p ∣ k + i
  · exact exists_prime_dvd_choose_of_large_prime_dvd_block hblock
  · have hle :=
    block_length_le_smoothNumbersUpTo_bound_of_no_large_prime_dvd_block (n := n) (k := k)
      hblock
    omega

end Nat.SylvesterSchur.Internal


-- created on 2026-10-23

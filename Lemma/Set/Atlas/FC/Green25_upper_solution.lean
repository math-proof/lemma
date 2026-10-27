import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.FC.Green25_upper_solution.Part8
open Asymptotics Filter Finset Green25


namespace Green25

/--
[encodeVector_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
private lemma encodeVector_injective (Q m : ℕ) :
  Function.Injective (@encodeVector Q m) := by
  intro v w h
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  simp only [encodeVector] at h
  omega

end Green25

namespace Green25

/--
[digit_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
lemma digit_counterexample
  {t : ℕ}
-- given
  (ht : 5 ≤ t) :
-- imply
  ¬ Property25 (candidate25 (2 ^ (4 * (2 ^ t) ^ 2))) (2 ^ (4 * (2 ^ t) ^ 2)) := by
-- proof
  intro h
  obtain ⟨P, hcard, hsmall⟩ := digit_partition t ht
  have hsmall' : 10 * #(P.parts.biUnion Finset.restrictedSumset) <
    2 ^ (4 * (2 ^ t) ^ 2) := by omega
  exact (not_le_of_gt hsmall') (h.2.2 P hcard)

end Green25

namespace Green25

/--
[scale25_exponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
private lemma scale25_exponent (t : ℕ) :
  4 * (2 ^ t) ^ 2 = 4 ^ (t + 1) := by
  conv_lhs =>
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [← pow_mul]
    rw [← pow_add]
  conv_rhs =>
    rw [show 4 = 2 ^ 2 by norm_num]
    rw [← pow_mul]
  congr 1
  omega

end Green25

namespace Green25

/--
[level25_good](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
private lemma level25_good (N : ℕ) (hL : 4 ^ 6 ≤ Nat.log 2 N) :
  5 ≤ level25 N ∧ scale25 (level25 N) ≤ N := by
  let L := Nat.log 2 N
  let u := Nat.log 4 L
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hu : 6 ≤ u := Nat.le_log_of_pow_le (by omega) (by simpa [L] using hL)
  have ht : level25 N + 1 = u := by
    change u - 1 + 1 = u
    omega
  have hN0 : N ≠ 0 := by
    intro h
    subst N
    simp [L] at hLpos
  have hE : 4 ^ (level25 N + 1) ≤ L := by
    rw [ht]
    exact Nat.pow_log_le_self 4 hLpos.ne'
  constructor
  · change 5 ≤ u - 1
    omega
  · rw [scale25, scale25_exponent]
    exact (Nat.pow_le_pow_right (by omega) hE).trans
      (Nat.pow_log_le_self 2 hN0)

end Green25

namespace Green25

/--
[selectedPartition25_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
private lemma selectedPartition25_spec (N : ℕ)
  (h : 5 ≤ level25 N ∧ scale25 (level25 N) ≤ N) :
  #(selectedPartition25 N).parts ≤
    (N / scale25 (level25 N) + 1) * candidate25 (scale25 (level25 N)) ∧
    10 * #((selectedPartition25 N).parts.biUnion Finset.restrictedSumset) < N := by
  rw [selectedPartition25, dif_pos h]
  simpa [scale25] using
    (Classical.choose_spec
      (tiled_digit_partition (level25 N) N h.1 (by simpa [scale25] using h.2)))

end Green25

namespace Green25

/--
[linear_le_pow25](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
private lemma linear_le_pow25 (u : ℕ) (hu : 5 ≤ u) : 4 + 4 * u ≤ 2 ^ u := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hu
  induction v with
  | zero => norm_num
  | succ v ih =>
    specialize ih (by omega)
    rw [show 5 + (v + 1) = (5 + v) + 1 by omega, pow_succ]
    have hp : 4 ≤ 2 ^ (5 + v) := by
      calc
        4 ≤ 2 ^ 5 := by norm_num
        _ ≤ 2 ^ (5 + v) := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
set_option maxHeartbeats 800000 in

end Green25

namespace Green25

/--
[green_25.upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
lemma green_25.upper
-- imply
  ∃ (candidateAnswer : ℕ → ℕ), let ans := (candidateAnswer : ℕ → ℕ) (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧ (fun N => (ans N : ℝ)) =o[atTop] bestUpper ∧ ∀ᶠ N in atTop, ¬ Property25 (ans N) N := by
-- proof
  let ans : ℕ → ℕ := fun N => #(selectedPartition25 N).parts
  refine ⟨ans, ?_, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (2 ^ (4 ^ 6))] with N hN
    have hL : 4 ^ 6 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) hN
    have hg := level25_good N hL
    have hN1 : 1 ≤ N := by
      calc
        1 ≤ 2 ^ (4 ^ 6) := one_le_pow₀ (by omega)
        _ ≤ N := hN
    constructor
    · change 1 ≤ #(selectedPartition25 N).parts
      exact ((selectedPartition25 N).parts_nonempty (by
        simp [hN1])).card_pos
    · change #(selectedPartition25 N).parts ≤ N
      simpa [Nat.card_Icc] using (selectedPartition25 N).card_parts_le_card
  · rw [Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨M : ℕ, hM⟩ := exists_nat_gt (64 / c)
    filter_upwards [eventually_ge_atTop (2 ^ (max (4 ^ 6) M))] with N hN
    let L := Nat.log 2 N
    let t := level25 N
    let B := scale25 t
    let D := 2 ^ (4 + 4 * t)
    have hLbig : max (4 ^ 6) M ≤ L := by
      exact Nat.le_log_of_pow_le (by omega) hN
    have hL : 4 ^ 6 ≤ L := (le_max_left _ _).trans hLbig
    have hLM : M ≤ L := (le_max_right _ _).trans hLbig
    have hg : 5 ≤ t ∧ B ≤ N := by
      simpa [L, t, B] using level25_good N (by simpa [L] using hL)
    have hspec := selectedPartition25_spec N (by simpa [t, B] using hg)
    have htpow : 4 + 4 * t ≤ 2 ^ t := linear_le_pow25 t hg.1
    have hd : 4 + 4 * t ≤ 4 * (2 ^ t) ^ 2 := by
      have hp : 1 ≤ 2 ^ t := one_le_pow₀ (by omega)
      nlinarith
    have hcandD : candidate25 B * D = B := by
      rw [show candidate25 B = 2 ^ (4 * (2 ^ t) ^ 2 - (4 + 4 * t)) by
        simpa [B, scale25, t] using candidate25_special t hg.1]
      simp only [D, ← pow_add, Nat.sub_add_cancel hd, B, scale25]
    have hqB : (N / B + 1) * B ≤ 2 * N := by
      calc
        (N / B + 1) * B ≤ N + B := by
          rw [Nat.add_mul]
          simpa using Nat.add_le_add_right (Nat.div_mul_le_self N B) B
        _ ≤ 2 * N := by omega
    have hansD : ans N * D ≤ 2 * N := by
      calc
        ans N * D ≤ ((N / B + 1) * candidate25 B) * D :=
          Nat.mul_le_mul_right D hspec.1
        _ = (N / B + 1) * B := by rw [mul_assoc, hcandD]
        _ ≤ 2 * N := hqB
    let u := Nat.log 4 L
    have hu : 6 ≤ u := Nat.le_log_of_pow_le (by omega) hL
    have htu : t + 1 = u := by
      change u - 1 + 1 = u
      omega
    have hLupper : L < 4 * 4 ^ (t + 1) := by
      have hh := Nat.lt_pow_succ_log_self (by omega : 1 < 4) L
      rw [show Nat.log 4 L = u by rfl, ← htu, pow_succ] at hh
      simpa [mul_comm] using hh
    have hDE : D = (4 ^ (t + 1)) ^ 2 := by
      simp only [D, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
      congr 1
      omega
    have hansL : ans N * L ^ 2 ≤ 32 * N := by
      have hsq : L ^ 2 ≤ 16 * D := by
        rw [hDE]
        nlinarith
      nlinarith
    have hN1 : 1 < N := by
      have hbase : 2 ^ (4 ^ 6) ≤ N :=
        (Nat.pow_le_pow_right (by omega) (le_max_left _ _)).trans hN
      have hpowbig : 1 < 2 ^ (4 ^ 6) := Nat.one_lt_two_pow (by norm_num)
      omega
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN1)
    have hlogle : Real.log (N : ℝ) ≤ 2 * (L : ℝ) := by
      have hpow := Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
      have hcast : (N : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by
        exact_mod_cast (Nat.le_of_lt (by simpa [L] using hpow))
      have hh := Real.strictMonoOn_log.monotoneOn
        (show (N : ℝ) ∈ Set.Ioi 0 by
          change (0 : ℝ) < N
          exact_mod_cast (Nat.zero_lt_of_lt hN1))
        (show (2 : ℝ) ^ (L + 1) ∈ Set.Ioi 0 by
          change (0 : ℝ) < (2 : ℝ) ^ (L + 1)
          positivity) hcast
      rw [Real.log_pow] at hh
      have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        norm_num at this ⊢
        exact this
      have hLone : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
      calc
        Real.log (N : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * Real.log 2 := hh
        _ ≤ ((L + 1 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
        _ ≤ 2 * (L : ℝ) := by push_cast; nlinarith
    have hcL : 64 < c * (L : ℝ) := by
      have hMc : 64 / c < (M : ℝ) := hM
      have hcpos : (0 : ℝ) < c := hc
      have hML : (M : ℝ) ≤ L := by exact_mod_cast hLM
      apply (div_lt_iff₀ hcpos).mp at hMc
      nlinarith
    have hansreal : (ans N : ℝ) * (L : ℝ) ^ 2 ≤ 32 * (N : ℝ) := by
      exact_mod_cast hansL
    have hmain : (ans N : ℝ) * Real.log (N : ℝ) ≤ c * (N : ℝ) := by
      have hansnonneg : (0 : ℝ) ≤ ans N := by positivity
      have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
      refine le_of_mul_le_mul_right ?_ hLpos
      calc
        ((ans N : ℝ) * Real.log (N : ℝ)) * (L : ℝ) ≤
          ((ans N : ℝ) * (2 * (L : ℝ))) * (L : ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogle hansnonneg) hLpos.le
        _ = 2 * ((ans N : ℝ) * (L : ℝ) ^ 2) := by ring
        _ ≤ 64 * (N : ℝ) := by nlinarith
        _ ≤ (c * (N : ℝ)) * (L : ℝ) := by
          have hh := mul_le_mul_of_nonneg_right hcL.le (show (0 : ℝ) ≤ N by positivity)
          nlinarith
    rw [show bestUpper N = (N : ℝ) / Real.log (N : ℝ) by rfl]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_pos (div_pos (by positivity) hlogpos)]
    have hdiv : (ans N : ℝ) ≤ (c * (N : ℝ)) / Real.log (N : ℝ) :=
      (le_div_iff₀ hlogpos).2 hmain
    calc
      (ans N : ℝ) ≤ (c * (N : ℝ)) / Real.log (N : ℝ) := hdiv
      _ = c * ((N : ℝ) / Real.log (N : ℝ)) := by ring
  · filter_upwards [eventually_ge_atTop (2 ^ (4 ^ 6))] with N hN
    have hL : 4 ^ 6 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by omega) hN
    have hg := level25_good N hL
    intro hprop
    have hsmall := (selectedPartition25_spec N hg).2
    exact (not_le_of_gt hsmall) (hprop.2.2 (selectedPartition25 N) rfl)

end Green25

/--
[candidate25_special](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
private lemma candidate25_special_eq
  {t : ℕ}
-- given
  (ht : 5 ≤ t) :
-- imply
  candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) = 2 ^ (4 * (2 ^ t) ^ 2 - (4 + 4 * t)) := by
-- proof
  apply Green25.candidate25_special t ht

/--
[complemented_digit_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
private lemma complemented_digit_partition_eq
  {Q m r : ℕ}
-- given
  (hQ : 2 ≤ Q)
  (heven : 2 ∣ Q)
  (hr : r ≤ m) :
-- imply
  ∃ P : Finpartition (Icc 1 (Q ^ m)), #P.parts = Q ^ m / 2 ^ r ∧ #(P.parts.biUnion Finset.restrictedSumset) ≤ r * (2 * Q) ^ (m - 1) := by
-- proof
  apply Green25.complemented_digit_partition Q m r hQ heven hr

/--
[digit_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
private lemma digit_partition_eq
  {t : ℕ}
-- given
  (ht : 5 ≤ t) :
-- imply
  ∃ P : Finpartition (Icc 1 (2 ^ (4 * (2 ^ t) ^ 2))), #P.parts = candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) ∧ 20 * #(P.parts.biUnion Finset.restrictedSumset) < 2 ^ (4 * (2 ^ t) ^ 2) := by
-- proof
  apply Green25.digit_partition t ht

/--
[tiled_digit_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean)
-/
@[path]
private lemma tiled_digit_partition_eq
  {t N : ℕ}
-- given
  (ht : 5 ≤ t)
  (hN : 2 ^ (4 * (2 ^ t) ^ 2) ≤ N) :
-- imply
  ∃ P : Finpartition (Icc 1 N), #P.parts ≤ (N / (2 ^ (4 * (2 ^ t) ^ 2)) + 1) * candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) ∧ 10 * #(P.parts.biUnion Finset.restrictedSumset) < N := by
-- proof
  apply Green25.tiled_digit_partition t N ht hN


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.MultiplicativeWeights
open Real Finset BigOperators MultiplicativeWeights


namespace MultiplicativeWeights

/--
[countRounds_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma countRounds_succ
  {n : ℕ}
  [DecidablePred P]
  {t : ℕ}
-- given
  (P : ℕ → Prop) :
-- imply
  countRounds P (t + 1) = countRounds P t + if P t then 1 else 0 := by
-- proof
  simp only [countRounds, Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp [Finset.mem_filter, Finset.mem_range]
  · rfl

end MultiplicativeWeights

namespace MultiplicativeWeights

/--
[weight_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma weight_succ
  {n : ℕ}
  [∀ i t, Decidable (wrong i t)]
  {ε : ℝ}
  {i : Fin n}
  {k : ℕ}
-- given
  (wrong : Fin n → ℕ → Prop) :
-- imply
  weight wrong ε i (k + 1) = weight wrong ε i k * if wrong i k then (1 - ε) else 1 := by
-- proof
  simp only [weight, expertMistakes, countRounds_succ]
  split_ifs with h <;> simp [pow_add, mul_comm]

end MultiplicativeWeights

namespace MultiplicativeWeights

variable {n : ℕ}
/--
[Φ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma Φ_zero (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
  (ε : ℝ) : Φ wrong ε 0 = (n : ℝ) := by
  simp [Φ, weight, expertMistakes, countRounds]

end MultiplicativeWeights

namespace MultiplicativeWeights

variable {n : ℕ}
/--
[Φ_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma Φ_step (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
  (ε : ℝ) (k : ℕ) :
  Φ wrong ε (k + 1) = Φ wrong ε k -
    ε * ∑ i ∈ (Finset.univ.filter (fun i => wrong i k)), weight wrong ε i k := by
  simp only [Φ, weight_succ]
  have key : ∀ i : Fin n,
    weight wrong ε i k * (if wrong i k then (1 - ε) else 1) =
    weight wrong ε i k - (if wrong i k then ε * weight wrong ε i k else 0) := by
    intro i; split_ifs with h <;> ring
  simp_rw [key, Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_filter]
  rw [Finset.mul_sum]

end MultiplicativeWeights

namespace MultiplicativeWeights

variable {n : ℕ}
/--
[Φ_drop_on_mistake](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma Φ_drop_on_mistake (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
  {ε : ℝ} (hε_pos : 0 < ε) (_hε_lt : ε < 1)
  (k : ℕ) (hmistake : algWrongAt wrong ε k) :
  Φ wrong ε (k + 1) ≤ (1 - ε / 2) * Φ wrong ε k := by
  rw [Φ_step]
  unfold algWrongAt at hmistake
  have hΦ_half : Φ wrong ε k / 2 ≤
    ∑ i ∈ (Finset.univ.filter (fun i => wrong i k)), weight wrong ε i k := by linarith
  have : ε * ∑ i ∈ (Finset.univ.filter (fun i => wrong i k)), weight wrong ε i k ≥
    ε / 2 * Φ wrong ε k := by
    have := mul_le_mul_of_nonneg_left hΦ_half (le_of_lt hε_pos)
    linarith
  linarith

end MultiplicativeWeights

namespace MultiplicativeWeights

variable {n : ℕ}
/--
[Φ_nonincreasing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma Φ_nonincreasing (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
  {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1) (k : ℕ) :
  Φ wrong ε (k + 1) ≤ Φ wrong ε k := by
  rw [Φ_step]
  have : 0 ≤ ε * ∑ i ∈ (Finset.univ.filter (fun i => wrong i k)), weight wrong ε i k := by
    apply mul_nonneg (le_of_lt hε_pos)
    apply Finset.sum_nonneg
    intro i _
    exact pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε) _
  linarith

end MultiplicativeWeights

namespace MultiplicativeWeights

variable {n : ℕ}
/--
[Φ_upper_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma Φ_upper_bound (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
  {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1)
  (T : ℕ) :
  Φ wrong ε T ≤ (n : ℝ) * (1 - ε / 2) ^ algMistakes wrong ε T := by
  classical
  induction T with
  | zero =>
    rw [Φ_zero]
    simp [algMistakes, countRounds]
  | succ T ih =>
    by_cases hmistake : algWrongAt wrong ε T
    ·
      have hstep := Φ_drop_on_mistake wrong hε_pos hε_lt T hmistake
      have halg : algMistakes wrong ε (T + 1) = algMistakes wrong ε T + 1 := by
        simp only [algMistakes, countRounds_succ]
        simp [hmistake]
      rw [halg]
      calc Φ wrong ε (T + 1)
        ≤ (1 - ε / 2) * Φ wrong ε T := hstep
        _ ≤ (1 - ε / 2) * ((n : ℝ) * (1 - ε / 2) ^ algMistakes wrong ε T) := by
          apply mul_le_mul_of_nonneg_left ih (by linarith)
        _ = (n : ℝ) * (1 - ε / 2) ^ (algMistakes wrong ε T + 1) := by
          rw [pow_succ]; ring
    ·
      have hstep := Φ_nonincreasing wrong hε_pos hε_lt T
      have halg : algMistakes wrong ε (T + 1) = algMistakes wrong ε T := by
        simp only [algMistakes, countRounds_succ]
        simp [hmistake]
      rw [halg]
      linarith

end MultiplicativeWeights

namespace MultiplicativeWeights

variable {n : ℕ}
/--
[Φ_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma Φ_lower_bound (wrong : Fin n → ℕ → Prop) [∀ i t, Decidable (wrong i t)]
  {ε : ℝ} (hε_lt : ε < 1) (i : Fin n) (t : ℕ) :
  weight wrong ε i t ≤ Φ wrong ε t := by
  apply Finset.single_le_sum (fun j _ => ?_) (Finset.mem_univ i)
  exact pow_nonneg (by linarith) _

end MultiplicativeWeights

namespace MultiplicativeWeights

/--
[log_one_sub_half_eps_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma log_one_sub_half_eps_le
  {n : ℕ}
  {ε : ℝ}
-- given
  (hε_lt : ε < 2) :
-- imply
  Real.log (1 - ε / 2) ≤ -ε / 2 := by
-- proof
  linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - ε / 2 by linarith)]

end MultiplicativeWeights

namespace MultiplicativeWeights

/--
[neg_log_one_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma neg_log_one_sub_le
  {n : ℕ}
  {ε : ℝ}
-- given
  (hε_pos : 0 < ε)
  (hε_le : ε ≤ 1/2) :
-- imply
  -Real.log (1 - ε) ≤ ε + ε ^ 2 := by
-- proof
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  suffices h : (1 - ε)⁻¹ ≤ Real.exp (ε + ε ^ 2) by
    have hlog : Real.log ((1 - ε)⁻¹) ≤ ε + ε ^ 2 := by
      rw [← Real.log_exp (ε + ε ^ 2)]
      exact Real.log_le_log (by positivity) h
    rwa [Real.log_inv] at hlog
  have step1 : (1 - ε)⁻¹ ≤ 1 + (ε + ε ^ 2) + (ε + ε ^ 2) ^ 2 / 2 := by
    rw [inv_le_iff_one_le_mul₀ h1ε]
    ring_nf
    have h1 : 0 ≤ ε ^ 2 := sq_nonneg ε
    have h2 : 1 - ε - ε ^ 2 - ε ^ 3 ≥ 0 := by nlinarith [sq_nonneg (1/2 - ε)]
    nlinarith [sq_nonneg ε, sq_nonneg (ε * ε)]
  calc (1 - ε)⁻¹
    ≤ 1 + (ε + ε ^ 2) + (ε + ε ^ 2) ^ 2 / 2 := step1
    _ ≤ Real.exp (ε + ε ^ 2) := by
      have h3 := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ ε + ε ^ 2 by nlinarith) 3
      simp only [sum_range_succ, range_zero, sum_empty, pow_zero, Nat.factorial,
        Nat.cast_one, pow_one] at h3
      linarith

end MultiplicativeWeights

namespace MultiplicativeWeights

/--
[potential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma potential_inequality
  {n : ℕ}
  [∀ i t, Decidable (wrong i t)]
  {ε : ℝ}
  {i : Fin n}
  {T : ℕ}
-- given
  (wrong : Fin n → ℕ → Prop)
  (hε_pos : 0 < ε)
  (hε_lt : ε < 1) :
-- imply
  (1 - ε) ^ expertMistakes wrong i T ≤ (n : ℝ) * (1 - ε / 2) ^ algMistakes wrong ε T := by
-- proof
  calc (1 - ε) ^ expertMistakes wrong i T
    = weight wrong ε i T := by rfl
    _ ≤ Φ wrong ε T := Φ_lower_bound wrong hε_lt i T
    _ ≤ (n : ℝ) * (1 - ε / 2) ^ algMistakes wrong ε T :=
      Φ_upper_bound wrong hε_pos hε_lt T

end MultiplicativeWeights

namespace MultiplicativeWeights

/--
[regret_bound_from_potential](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma regret_bound_from_potential
  {n : ℕ}
  {n : ℕ}
  {ε : ℝ}
  {m mᵢ : ℕ}
-- given
  (hn : 0 < n)
  (hε_pos : 0 < ε)
  (hε_le : ε ≤ 1/2)
  (hpot : (1 - ε) ^ mᵢ ≤ (n : ℝ) * (1 - ε / 2) ^ m) :
-- imply
  (m : ℝ) ≤ 2 * Real.log n / ε + 2 * (1 + ε) * mᵢ := by
-- proof
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have h1ε2 : (0 : ℝ) < 1 - ε / 2 := by linarith
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hε_ne : ε ≠ 0 := ne_of_gt hε_pos
  have hlog : (mᵢ : ℝ) * Real.log (1 - ε) ≤ Real.log n + (m : ℝ) * Real.log (1 - ε / 2) := by
    have h1 := Real.log_le_log (by positivity) hpot
    rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    linarith
  have hlog2 : (m : ℝ) * (-Real.log (1 - ε / 2)) ≤
    Real.log n + (mᵢ : ℝ) * (-Real.log (1 - ε)) := by linarith
  have hlog_lb : ε / 2 ≤ -Real.log (1 - ε / 2) := by
    linarith [log_one_sub_half_eps_le (show ε < 2 by linarith)]
  have hstep3 : (m : ℝ) * (ε / 2) ≤ (m : ℝ) * (-Real.log (1 - ε / 2)) :=
    mul_le_mul_of_nonneg_left hlog_lb (Nat.cast_nonneg m)
  have hlog_ub : -Real.log (1 - ε) ≤ ε + ε ^ 2 := neg_log_one_sub_le hε_pos hε_le
  have hstep4 : (mᵢ : ℝ) * (-Real.log (1 - ε)) ≤ (mᵢ : ℝ) * (ε + ε ^ 2) :=
    mul_le_mul_of_nonneg_left hlog_ub (Nat.cast_nonneg mᵢ)
  have hcombine : (m : ℝ) * (ε / 2) ≤ Real.log n + (mᵢ : ℝ) * (ε + ε ^ 2) := by linarith
  have h : (m : ℝ) * (ε / 2) * (2 / ε) ≤
    (Real.log n + (mᵢ : ℝ) * (ε + ε ^ 2)) * (2 / ε) :=
    mul_le_mul_of_nonneg_right hcombine (div_nonneg two_pos.le (le_of_lt hε_pos))
  have hsimp : (m : ℝ) * (ε / 2) * (2 / ε) = (m : ℝ) := by field_simp
  rw [hsimp] at h
  calc (m : ℝ) ≤ (Real.log n + (mᵢ : ℝ) * (ε + ε ^ 2)) * (2 / ε) := h
    _ = 2 * Real.log n / ε + 2 * (1 + ε) * mᵢ := by field_simp

end MultiplicativeWeights

namespace MultiplicativeWeights

/--
[weighted_majority_regret_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma weighted_majority_regret_bound
  {n : ℕ}
  {n : ℕ}
  [∀ i t, Decidable (wrong i t)]
  {ε : ℝ}
  {i : Fin n}
  {T : ℕ}
-- given
  (hn : 0 < n)
  (wrong : Fin n → ℕ → Prop)
  (hε_pos : 0 < ε)
  (hε_le : ε ≤ 1/2) :
-- imply
  (algMistakes wrong ε T : ℝ) ≤ 2 * Real.log n / ε + 2 * (1 + ε) * expertMistakes wrong i T := by
-- proof
  exact regret_bound_from_potential hn hε_pos hε_le
    (potential_inequality wrong hε_pos (by linarith) i T)

end MultiplicativeWeights

namespace MultiplicativeWeights

/--
[expert_penalty_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma expert_penalty_split
  {n : ℕ}
  {M : Fin n → P → ℝ}
  {outcomes : ℕ → P}
  {i : Fin n}
  {T : ℕ} :
-- imply
  totalExpertPenalty M outcomes i T = totalNonnegPenalty M outcomes i T + totalNegPenalty M outcomes i T := by
-- proof
  classical
  simp only [totalExpertPenalty, totalNonnegPenalty, totalNegPenalty]
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun t => M i (outcomes t) ≥ 0)]
  congr 1
  apply Finset.sum_congr
  · ext t
    simp only [Finset.mem_filter, not_le]
  · intros; rfl

end MultiplicativeWeights

namespace MultiplicativeWeights

/--
[corollary_algebraic_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma corollary_algebraic_core
  {n : ℕ}
  {totalExp expertTotal A B ρ logn δ : ℝ}
  {T : ℕ}
-- given
  (hT_pos : (0 : ℝ) < T)
  (hρ_pos : 0 < ρ)
  (hδ_pos : 0 < δ)
  (hAB : A + B = expertTotal)
  (hAmB : A - B ≤ T * ρ)
  (hbound : totalExp ≤ ρ * logn / (δ / (4 * ρ)) + (1 + δ / (4 * ρ)) * A + (1 - δ / (4 * ρ)) * B)
  (hT_big : 16 * ρ ^ 2 * logn / δ ^ 2 ≤ T) :
-- imply
  totalExp / T ≤ δ + expertTotal / T := by
-- proof
  have hε_pos : 0 < δ / (4 * ρ) := div_pos hδ_pos (by positivity)
  have h4 : ρ * logn / (δ / (4 * ρ)) = 4 * ρ ^ 2 * logn / δ := by
    field_simp
  have h2 : δ / (4 * ρ) * (A - B) ≤ δ * ↑T / 4 := by
    have hmul := mul_le_mul_of_nonneg_left hAmB (le_of_lt hε_pos)
    have h3 : δ / (4 * ρ) * (↑T * ρ) = δ * ↑T / 4 := by
      field_simp
    linarith
  have h1 : (1 + δ / (4 * ρ)) * A + (1 - δ / (4 * ρ)) * B =
    expertTotal + δ / (4 * ρ) * (A - B) := by rw [← hAB]; ring
  have h5 : totalExp ≤ 4 * ρ ^ 2 * logn / δ + expertTotal + δ * ↑T / 4 := by linarith
  rw [div_le_iff₀ hT_pos]
  have hT_ne : (↑T : ℝ) ≠ 0 := ne_of_gt hT_pos
  rw [add_mul, div_mul_cancel₀ _ hT_ne]
  have hδ2_pos : (0 : ℝ) < δ ^ 2 := by positivity
  have hTδ2 : ↑T * δ ^ 2 ≥ 16 * ρ ^ 2 * logn := by
    have := (div_le_iff₀ hδ2_pos).mp hT_big; linarith
  have h_ineq : 4 * ρ ^ 2 * logn / δ ≤ ↑T * δ / 4 := by
    rw [div_le_div_iff₀ hδ_pos (by norm_num : (0:ℝ) < 4)]
    nlinarith
  linarith [mul_pos hδ_pos hT_pos]

end MultiplicativeWeights

namespace MultiplicativeWeights

/--
[abs_penalty_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/MultiplicativeWeights.lean)
-/
@[path]
lemma abs_penalty_sum_le
  {n : ℕ}
  {M : Fin n → P → ℝ}
  {outcomes : ℕ → P}
  {i : Fin n}
  {T : ℕ}
-- given
  (hM : ∀ i j, M i j ∈ Set.Icc (-ρ) ρ)
  (_hρ_pos : 0 < ρ) :
-- imply
  totalNonnegPenalty M outcomes i T - totalNegPenalty M outcomes i T ≤ T * ρ := by
-- proof
  classical
  simp only [totalNonnegPenalty, totalNegPenalty]
  have habs : ∑ t ∈ Finset.range T, |M i (outcomes t)| ≤ T * ρ := by
    calc ∑ t ∈ Finset.range T, |M i (outcomes t)|
      ≤ ∑ t ∈ Finset.range T, ρ := by
        apply Finset.sum_le_sum; intro t _
        exact abs_le.mpr ⟨by linarith [(hM i (outcomes t)).1], (hM i (outcomes t)).2⟩
      _ = T * ρ := by simp [Finset.sum_const, nsmul_eq_mul]
  suffices h : ∑ t ∈ (Finset.range T).filter (fun t => M i (outcomes t) ≥ 0), M i (outcomes t) -
    ∑ t ∈ (Finset.range T).filter (fun t => M i (outcomes t) < 0), M i (outcomes t) ≤
    ∑ t ∈ Finset.range T, |M i (outcomes t)| from le_trans h habs
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range T) (fun t => M i (outcomes t) ≥ 0)]
  have hfilt : (Finset.range T).filter (fun t => ¬M i (outcomes t) ≥ 0) =
    (Finset.range T).filter (fun t => M i (outcomes t) < 0) := by
    ext t; simp only [Finset.mem_filter, not_le]
  rw [hfilt]
  have hnn : ∀ t ∈ (Finset.range T).filter (fun t => M i (outcomes t) ≥ 0),
    |M i (outcomes t)| = M i (outcomes t) := by
    intro t ht; simp only [Finset.mem_filter] at ht; exact abs_of_nonneg ht.2
  have hng : ∀ t ∈ (Finset.range T).filter (fun t => M i (outcomes t) < 0),
    |M i (outcomes t)| = -M i (outcomes t) := by
    intro t ht; simp only [Finset.mem_filter] at ht; exact abs_of_neg ht.2
  rw [Finset.sum_congr rfl hnn, Finset.sum_congr rfl hng]
  linarith [Finset.sum_neg_distrib (s := (Finset.range T).filter (fun t => M i (outcomes t) < 0))
    (f := fun t => M i (outcomes t))]

end MultiplicativeWeights


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter5.Hajos
open Filter Topology Real Asymptotics SimpleGraph Hajos


namespace Hajos

/--
[hajosParam_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma hajosParam_ge
  {n : ℕ} :
-- imply
  10 * Real.sqrt (n : ℝ) ≤ (hajosParam n : ℝ) :=
-- proof
  Nat.le_ceil _

end Hajos

namespace Hajos

/--
[hajosParam_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma hajosParam_le
  {n : ℕ} :
-- imply
  (hajosParam n : ℝ) ≤ 10 * Real.sqrt (n : ℝ) + 1 :=
-- proof
  (Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).le

end Hajos

namespace Hajos

/--
[hajosParam_sq_ge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma hajosParam_sq_ge
  {n : ℕ} :
-- imply
  100 * (n : ℝ) ≤ ((hajosParam n : ℕ) : ℝ) ^ 2 := by
-- proof
  have h := hajosParam_ge n
  have ht_nn : (0 : ℝ) ≤ ((hajosParam n : ℕ) : ℝ) := Nat.cast_nonneg _
  have h10_nn : (0:ℝ) ≤ 10 * Real.sqrt (n : ℝ) := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc (100 : ℝ) * (n : ℝ) = (10 * Real.sqrt (n : ℝ)) ^ 2 := by
    rw [mul_pow, sq_sqrt (Nat.cast_nonneg n)]; ring
    _ ≤ ((hajosParam n : ℕ) : ℝ) ^ 2 := sq_le_sq' (by linarith) h

end Hajos

namespace Hajos

/--
[subdivisionUnionBound_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma subdivisionUnionBound_nonneg
  {n : ℕ} :
-- imply
  0 ≤ subdivisionUnionBound n := by
-- proof
  unfold subdivisionUnionBound
  exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)

end Hajos

namespace Hajos

/--
[log_le_sqrt_div_ten](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma log_le_sqrt_div_ten
-- imply
  ∀ᶠ (n : ℕ) in atTop, Real.log (n : ℝ) ≤ (1/10) * Real.sqrt (n : ℝ) := by
-- proof
  have h := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).bound
    (show (0:ℝ) < 1/10 by norm_num)
  rw [Filter.eventually_atTop] at h ⊢
  obtain ⟨N, hN⟩ := h
  refine ⟨max (Nat.ceil N) 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnN : N ≤ (n : ℝ) := by
    calc N ≤ ↑(Nat.ceil N) := Nat.le_ceil N
    _ ≤ ↑(max (Nat.ceil N) 1) := by exact_mod_cast le_max_left _ _
    _ ≤ ↑n := by exact_mod_cast hn
  have h1 := hN (n : ℝ) hnN
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0:ℝ) ≤ n) _)] at h1
  rw [Real.norm_of_nonneg (Real.log_nonneg hnR)] at h1
  rw [Real.sqrt_eq_rpow]; linarith

end Hajos

namespace Hajos

/--
[hajosParam_log_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma hajosParam_log_bound
-- imply
  ∀ᶠ (n : ℕ) in atTop, (hajosParam n : ℝ) * Real.log (n : ℝ) ≤ 2 * (n : ℝ) := by
-- proof
  filter_upwards [log_le_sqrt_div_ten, Filter.eventually_ge_atTop 1] with n hlog hn1
  have ht_le := hajosParam_le n
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsqrt_le_n : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have := Real.sqrt_le_sqrt (show (n:ℝ) ≤ (n:ℝ)^2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith : (0:ℝ) ≤ n)] at this
  have step1 : (hajosParam n : ℝ) * Real.log (n : ℝ)
    ≤ (10 * Real.sqrt (n : ℝ) + 1) * ((1/10) * Real.sqrt (n : ℝ)) := by
    gcongr
  have step2 : (10 * Real.sqrt (n : ℝ) + 1) * ((1/10) * Real.sqrt (n : ℝ))
    = Real.sqrt (n : ℝ) ^ 2 + (1/10) * Real.sqrt (n : ℝ) := by ring
  have step3 : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := sq_sqrt (Nat.cast_nonneg n)
  linarith

end Hajos

namespace Hajos

/--
[pow_eq_exp_mul_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma pow_eq_exp_mul_log
  {n : ℕ}
  {t : ℕ}
-- given
  (hn : 0 < (n : ℝ)) :
-- imply
  (n : ℝ) ^ t = Real.exp ((t : ℝ) * Real.log (n : ℝ)) := by
-- proof
  rw [← Real.rpow_natCast (n : ℝ) t, Real.rpow_def_of_pos hn]
  ring_nf

end Hajos

namespace Hajos

/--
[tendsto_exp_neg_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma tendsto_exp_neg_nat
-- imply
  Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (nhds 0) :=
-- proof
  Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

end Hajos

namespace Hajos

/--
[subdivisionUnionBound_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma subdivisionUnionBound_le_exp
-- imply
  ∀ᶠ (n : ℕ) in atTop, subdivisionUnionBound n ≤ Real.exp (-(n : ℝ)) := by
-- proof
  filter_upwards [hajosParam_log_bound, Filter.eventually_ge_atTop 1] with n hlog hn1
  unfold subdivisionUnionBound
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  calc (n.choose (hajosParam n) : ℝ) * Real.exp (-(hajosParam n : ℝ) ^ 2 / 10)
    ≤ (n : ℝ) ^ (hajosParam n) * Real.exp (-(hajosParam n : ℝ) ^ 2 / 10) := by
      gcongr; exact_mod_cast Nat.choose_le_pow n (hajosParam n)
    _ = Real.exp ((hajosParam n : ℝ) * Real.log (n : ℝ) +
      (-(hajosParam n : ℝ) ^ 2 / 10)) := by
      rw [pow_eq_exp_mul_log n hn' (hajosParam n), ← Real.exp_add]
    _ ≤ Real.exp (-(n : ℝ)) := by
      apply Real.exp_le_exp_of_le; linarith [hajosParam_sq_ge n]

end Hajos

namespace Hajos

/--
[subdivision_union_bound_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma subdivision_union_bound_tendsto_zero
-- imply
  Tendsto subdivisionUnionBound atTop (nhds 0) := by
-- proof
  apply squeeze_zero'
  · filter_upwards with n using subdivisionUnionBound_nonneg n
  · filter_upwards [subdivisionUnionBound_le_exp] with n hn using hn
  · exact tendsto_exp_neg_nat

end Hajos

namespace Hajos

/--
[hajos_conjecture_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter5/Hajos.lean)
-/
@[path]
lemma hajos_conjecture_counterexample
  {probKtSubdiv : ℕ → ℝ}
-- given
  (hP_nonneg : ∀ n, 0 ≤ probKtSubdiv n)
  (hP_le : ∀ n, probKtSubdiv n ≤ subdivisionUnionBound n) :
-- imply
  Tendsto probKtSubdiv atTop (nhds 0) :=
-- proof
  tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds
    subdivision_union_bound_tendsto_zero
    hP_nonneg
    hP_le

end Hajos


-- created on 2026-10-23

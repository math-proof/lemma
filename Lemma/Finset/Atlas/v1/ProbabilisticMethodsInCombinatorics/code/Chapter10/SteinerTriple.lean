import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.SteinerTriple
open MeasureTheory Filter Topology Real Set


/--
[integral_log_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean)
-/
@[path]
lemma integral_log_sq
-- imply
  ∫ (t : ℝ) in (0:ℝ)..1, Real.log (t ^ 2) = -2 := by
-- proof
  have h1 : ∫ (t : ℝ) in (0:ℝ)..1, Real.log (t ^ 2) =
    ∫ (t : ℝ) in (0:ℝ)..1, 2 * Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1)] at ht
    simp only; rw [Real.log_pow]; norm_cast
  rw [h1, intervalIntegral.integral_const_mul, integral_log_from_zero]
  simp [Real.log_one]

/--
[antitone_log_inv_add_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean)
-/
@[path]
lemma antitone_log_inv_add_sq
  {t : ℝ} :
-- imply
  Antitone (fun n : ℕ => Real.log (1/(↑n + 4 : ℝ) + t ^ 2)) := by
-- proof
  intro m n hmn
  apply Real.log_le_log (by positivity)
  have h : (↑m : ℝ) + 4 ≤ (↑n : ℝ) + 4 := by exact_mod_cast Nat.add_le_add_right hmn 4
  have hm_pos : (0 : ℝ) < ↑m + 4 := by positivity
  linarith [div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ 1) hm_pos h]

/--
[tendsto_log_inv_add_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean)
-/
@[path]
lemma tendsto_log_inv_add_sq
  {t : ℝ}
-- given
  (ht : t ≠ 0) :
-- imply
  Tendsto (fun n : ℕ => Real.log (1/(↑n + 4 : ℝ) + t ^ 2)) atTop (nhds (Real.log (t ^ 2))) := by
-- proof
  apply Tendsto.log
  · have h1 : Tendsto (fun n : ℕ => (↑n : ℝ) + 4) atTop atTop :=
    Filter.tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => 1/(↑n + 4 : ℝ)) atTop (nhds 0) := by
      simp_rw [one_div]
      exact tendsto_inv_atTop_zero.comp h1
    simpa using h2.add (tendsto_const_nhds (x := t^2))
  · exact pow_ne_zero 2 ht

/--
[integrableOn_log_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean)
-/
@[path]
lemma integrableOn_log_sq
-- imply
  IntegrableOn (fun t : ℝ => Real.log (t ^ 2)) (Ioc 0 1) volume := by
-- proof
  rw [show (fun t : ℝ => Real.log (t ^ 2)) = (fun t => (2 : ℕ) * Real.log t) from by
    ext x; rw [Real.log_pow]]
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ 1)]
  exact intervalIntegral.intervalIntegrable_of_integral_ne_zero (by
    rw [show ∫ (t : ℝ) in (0:ℝ)..1, (2 : ℕ) * Real.log t =
      (2 : ℕ) * ∫ (t : ℝ) in (0:ℝ)..1, Real.log t from
      intervalIntegral.integral_const_mul _ _]
    rw [integral_log_from_zero]; simp [Real.log_one])

/--
[integrableOn_log_inv_add_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean)
-/
@[path]
lemma integrableOn_log_inv_add_sq
  {n : ℕ} :
-- imply
  IntegrableOn (fun t => Real.log (1/(↑n + 4 : ℝ) + t ^ 2)) (Ioc 0 1) volume := by
-- proof
  apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply ContinuousOn.log
  · exact continuousOn_const.add (continuous_pow 2).continuousOn
  · intro x _; positivity

/--
[tendsto_integral_log_inv_add_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean)
-/
@[path]
lemma tendsto_integral_log_inv_add_sq
-- imply
  Tendsto (fun n : ℕ => ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1/(↑n + 4 : ℝ) + t ^ 2)) atTop (nhds (-2)) := by
-- proof
  rw [← integral_log_sq]
  simp_rw [intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1)]
  apply integral_tendsto_of_tendsto_of_antitone
  · exact fun n => (integrableOn_log_inv_add_sq n).integrable
  · exact integrableOn_log_sq.integrable
  · exact ae_of_all _ (fun t => antitone_log_inv_add_sq t)
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ (fun t ht => tendsto_log_inv_add_sq (ne_of_gt ht.1))

/--
[integral_log_one_add_mul_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/SteinerTriple.lean)
-/
@[path]
lemma integral_log_one_add_mul_sq
  {c : ℝ}
-- given
  (hc : 0 < c) :
-- imply
  ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1 + c * t ^ 2) = Real.log c + ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1/c + t ^ 2) := by
-- proof
  have heq : (fun t : ℝ => Real.log (1 + c * t ^ 2)) =
    (fun t => Real.log c + Real.log (1/c + t ^ 2)) := by
    ext t
    have hpos : (0 : ℝ) < 1/c + t^2 := by positivity
    rw [← Real.log_mul (ne_of_gt hc) (ne_of_gt hpos)]
    congr 1; field_simp
  rw [heq, intervalIntegral.integral_add]
  · simp [intervalIntegral.integral_const]
  · exact intervalIntegrable_const
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log
    · exact continuousOn_const.add (continuous_pow 2).continuousOn
    · intro x _; positivity
/-- Entropy upper bound on Steiner triple systems: for $n \ge 4$,
$\log |\mathrm{STS}(n)| \le \tfrac{n(n-1)}{6} \int_0^1 \log(1 + (n-3) t^2) \, dt$. -/


-- created on 2026-10-23

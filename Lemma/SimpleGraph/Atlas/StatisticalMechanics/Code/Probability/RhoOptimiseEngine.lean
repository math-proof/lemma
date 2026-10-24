import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.RhoOptimiseEngine
open Finset Real Filter Topology intervalIntegral MeasureTheory StatMech StatMech.Probability


/--
[roe_integral_exp_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_integral_exp_mul_eq
  {c : ℝ}
  {a b : ℝ}
-- given
  (hc : c ≠ 0) :
-- imply
  ∫ x in a..b, Real.exp (c * x) = (Real.exp (c * b) - Real.exp (c * a)) / c := by
-- proof
  apply StatMech.Probability.roe_integral_exp_mul c hc a b

/--
[roe_integral_exp_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_integral_exp_le_eq
  {t : ℝ}
-- given
  (ht : 0 < t) :
-- imply
  (∫ u in (0:ℝ)..1, Real.exp (-(t / 2) * u)) ≤ 2 / t := by
-- proof
  apply StatMech.Probability.roe_integral_exp_le t ht

/--
[roe_integral_one_sub_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_integral_one_sub_pow_eq
  {n : ℕ} :
-- imply
  ∫ u in (0:ℝ)..1, (1 - u) ^ n = 1 / (n + 1) := by
-- proof
  apply StatMech.Probability.roe_integral_one_sub_pow n

/--
[roe_rpow_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_rpow_integrable_eq
  {δ : ℝ}
-- given
  (hδ0 : 0 < δ) :
-- imply
  IntervalIntegrable (fun u => δ ^ (u / (2 - u))) MeasureTheory.volume 0 1 := by
-- proof
  apply StatMech.Probability.roe_rpow_integrable δ hδ0

/--
[roe_integral_rhs_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_integral_rhs_le_eq
  {δ : ℝ}
-- given
  (hδ0 : 0 < δ)
  (hδ1 : δ < 1) :
-- imply
  (∫ u in (0:ℝ)..1, δ ^ (u / (2 - u))) ≤ 2 / (-(Real.log δ)) := by
-- proof
  apply StatMech.Probability.roe_integral_rhs_le δ hδ0 hδ1

/--
[roe_W_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_W_nonneg_eq
  [Fintype ι]
  {d : ι → ℕ}
  {c : ι → ℝ}
-- given
  (hc : ∀ i, 0 ≤ c i) :
-- imply
  0 ≤ roe_W d c := by
-- proof
  apply StatMech.Probability.roe_W_nonneg hc

/--
[roe_V_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_V_nonneg_eq
  [Fintype ι]
  {d : ι → ℕ}
  {c : ι → ℝ}
-- given
  (hc : ∀ i, 0 ≤ c i) :
-- imply
  0 ≤ roe_V d c := by
-- proof
  apply StatMech.Probability.roe_V_nonneg hc

/--
[roe_summand_intervalIntegrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_summand_intervalIntegrable_eq
  [Fintype ι]
  {d : ι → ℕ}
  {c : ι → ℝ}
  {i : ι} :
-- imply
  IntervalIntegrable (fun u => (d i : ℝ) * (1 - u) ^ (d i - 1) * c i) MeasureTheory.volume 0 1 := by
-- proof
  apply StatMech.Probability.roe_summand_intervalIntegrable d c i

/--
[roe_integral_summand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_integral_summand_eq
  [Fintype ι]
  {d : ι → ℕ}
  {c : ι → ℝ}
  {i : ι} :
-- imply
  (∫ u in (0:ℝ)..1, (d i : ℝ) * (1 - u) ^ (d i - 1) * c i) = (if d i = 0 then 0 else c i) := by
-- proof
  apply StatMech.Probability.roe_integral_summand d c i

/--
[roe_integral_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_integral_lhs_eq
  [Fintype ι]
  {d : ι → ℕ}
  {c : ι → ℝ} :
-- imply
  (∫ u in (0:ℝ)..1, roe_lhs d c u) = roe_V d c := by
-- proof
  apply StatMech.Probability.roe_integral_lhs d c

/--
[roe_logGain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_logGain_eq
  [Fintype ι]
  {d : ι → ℕ}
  {c : ι → ℝ}
  {δ : ℝ}
-- given
  (hc : ∀ i, 0 ≤ c i)
  (hδ : 0 ≤ δ)
  (Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → roe_lhs d c u ≤ δ ^ (u / (2 - u)) * roe_W d c) :
-- imply
  roe_V d c * Real.log (1 / δ) ≤ 2 * roe_W d c := by
-- proof
  apply StatMech.Probability.roe_logGain hc hδ Hmaster

/--
[roe_logGain_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/RhoOptimiseEngine.lean)
-/
@[path]
private lemma roe_logGain_four_eq
  [Fintype ι]
  {d : ι → ℕ}
  {c : ι → ℝ}
  {δ : ℝ}
-- given
  (hc : ∀ i, 0 ≤ c i)
  (hδ : 0 ≤ δ)
  (Hmaster : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → (∑ i : ι, 4 * (d i : ℝ) * (1 - u) ^ (d i - 1) * c i) ≤ δ ^ (u / (2 - u)) * (∑ i : ι, 4 * (d i : ℝ) * c i)) :
-- imply
  2 * (∑ i ∈ univ.filter (fun i => d i ≠ 0), c i) * Real.log (1 / δ) ≤ ∑ i : ι, 4 * (d i : ℝ) * c i := by
-- proof
  apply StatMech.Probability.roe_logGain_four hc hδ Hmaster


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDualGapAsymptotic.Part2
open Filter Topology StatMech StatMech.FrontierD


/--
[two_mul_le_log_one_add_div_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma two_mul_le_log_one_add_div_one_sub_eq
  {t : Real}
-- given
  (ht0 : 0 <= t)
  (ht1 : t < 1) :
-- imply
  2 * t <= Real.log ((1 + t) / (1 - t)) := by
-- proof
  apply StatMech.FrontierD.two_mul_le_log_one_add_div_one_sub ht0 ht1

/--
[log_one_add_div_one_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma log_one_add_div_one_sub_le_eq
  {t : Real}
-- given
  (ht0 : 0 <= t)
  (ht1 : t < 1) :
-- imply
  Real.log ((1 + t) / (1 - t)) <= 2 * t / (1 - t) := by
-- proof
  apply StatMech.FrontierD.log_one_add_div_one_sub_le ht0 ht1

/--
[sixVertexDualGapPowerTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma sixVertexDualGapPowerTerm_nonneg_eq
  {x : Real}
  {n : Nat}
-- given
  (hx0 : 0 <= x)
  (hx1 : x < 1) :
-- imply
  0 <= sixVertexDualGapPowerTerm x n := by
-- proof
  apply StatMech.FrontierD.sixVertexDualGapPowerTerm_nonneg hx0 hx1 n

/--
[sixVertexDualGapPowerTerm_le_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma sixVertexDualGapPowerTerm_le_geometric_eq
  {x : Real}
  {n : Nat}
-- given
  (hx0 : 0 <= x)
  (hx1 : x < 1) :
-- imply
  sixVertexDualGapPowerTerm x n <= (8 / (1 - x)) * x ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDualGapPowerTerm_le_geometric hx0 hx1 n

/--
[summable_sixVertexDualGapPowerTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma summable_sixVertexDualGapPowerTerm_eq
  {x : Real}
-- given
  (hx0 : 0 <= x)
  (hx1 : x < 1) :
-- imply
  Summable (sixVertexDualGapPowerTerm x) := by
-- proof
  apply StatMech.FrontierD.summable_sixVertexDualGapPowerTerm hx0 hx1

/--
[tsum_geometric_nat_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma tsum_geometric_nat_succ_eq
  {x : Real}
-- given
  (hx0 : 0 <= x)
  (hx1 : x < 1) :
-- imply
  (∑' n : Nat, x ^ (n + 1)) = x / (1 - x) := by
-- proof
  apply StatMech.FrontierD.tsum_geometric_nat_succ hx0 hx1

/--
[sixVertexDualGapPowerSeries_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma sixVertexDualGapPowerSeries_lower_eq
  {x : Real}
-- given
  (hx0 : 0 <= x)
  (hx1 : x < 1) :
-- imply
  8 * x <= sixVertexDualGapPowerSeries x := by
-- proof
  apply StatMech.FrontierD.sixVertexDualGapPowerSeries_lower hx0 hx1

/--
[sixVertexDualGapPowerSeries_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma sixVertexDualGapPowerSeries_upper_eq
  {x : Real}
-- given
  (hx0 : 0 <= x)
  (hx1 : x < 1) :
-- imply
  sixVertexDualGapPowerSeries x <= 8 * x / (1 - x) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDualGapPowerSeries_upper hx0 hx1

/--
[sixVertexDualGapPowerSeries_div_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma sixVertexDualGapPowerSeries_div_tendsto_one_eq :
-- imply
  Tendsto (fun x : Real => sixVertexDualGapPowerSeries x / (8 * x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDualGapPowerSeries_div_tendsto_one

/--
[sixVertexDualGapRate_div_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDualGapAsymptotic.lean)
-/
@[path]
private lemma sixVertexDualGapRate_div_tendsto_one_eq :
-- imply
  Tendsto (fun lam : Real => sixVertexDualGapRate lam / (8 * Real.exp (-(Real.pi ^ 2) / (2 * lam)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDualGapRate_div_tendsto_one


-- created on 2026-10-23

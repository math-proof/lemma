import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedHadamardPrereq
open Finset StatMech StatMech.FrontierA


/--
[finiteIsingWeightedFieldRadius_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedHadamardPrereq.lean)
-/
@[path]
private lemma finiteIsingWeightedFieldRadius_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {a : V → Real} :
-- imply
  0 ≤ finiteIsingWeightedFieldRadius a := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedFieldRadius_nonneg a

/--
[norm_weightedSpinSum_le_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedHadamardPrereq.lean)
-/
@[path]
private lemma norm_weightedSpinSum_le_radius_eq
  [Fintype V]
  [DecidableEq V]
  {a : V → Real}
  {s : ConfigSpace V} :
-- imply
  ‖∑ v : V, (a v : Complex) * spin s v‖ ≤ finiteIsingWeightedFieldRadius a := by
-- proof
  apply StatMech.FrontierA.norm_weightedSpinSum_le_radius a s

/--
[finiteIsingWeightedFieldPartition_analyticOnNhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedHadamardPrereq.lean)
-/
@[path]
private lemma finiteIsingWeightedFieldPartition_analyticOnNhd_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {a : V → Real} :
-- imply
  AnalyticOnNhd Complex (finiteIsingWeightedFieldPartition G beta a) Set.univ := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedFieldPartition_analyticOnNhd beta a

/--
[finiteIsingWeightedFieldPartition_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedHadamardPrereq.lean)
-/
@[path]
private lemma finiteIsingWeightedFieldPartition_zero_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {a : V → Real} :
-- imply
  finiteIsingWeightedFieldPartition G beta a 0 = ∑ s : ConfigSpace V, (zeroFieldInteractionWeight G beta s : Complex) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedFieldPartition_zero beta a

/--
[finiteIsingWeightedFieldPartition_zero_re_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedHadamardPrereq.lean)
-/
@[path]
private lemma finiteIsingWeightedFieldPartition_zero_re_pos_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {a : V → Real} :
-- imply
  0 < (finiteIsingWeightedFieldPartition G beta a 0).re := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedFieldPartition_zero_re_pos beta a

/--
[norm_finiteIsingWeightedFieldPartition_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedHadamardPrereq.lean)
-/
@[path]
private lemma norm_finiteIsingWeightedFieldPartition_le_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {a : V → Real}
  {z : Complex} :
-- imply
  ‖finiteIsingWeightedFieldPartition G beta a z‖ ≤ (∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s) * Real.exp (‖z‖ * finiteIsingWeightedFieldRadius a) := by
-- proof
  apply StatMech.FrontierA.norm_finiteIsingWeightedFieldPartition_le beta a z


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonSupport
open Finset StatMech StatMech.FrontierA


/--
[gaugeWilsonSurfaceTerm_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonSupport.lean)
-/
@[path]
private lemma gaugeWilsonSurfaceTerm_pos_eq
  [Fintype E]
  [DecidableEq E]
  {K : P → ℝ}
  {A : Finset P}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  0 < ∏ p ∈ A, Real.tanh (K p) := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonSurfaceTerm_pos K hK A

/--
[abs_wilsonSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonSupport.lean)
-/
@[path]
private lemma abs_wilsonSpin_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
  {omega : GaugeConfig E} :
-- imply
  |wilsonSpin L omega| = 1 := by
-- proof
  apply StatMech.FrontierA.abs_wilsonSpin L omega

/--
[abs_gaugeWilsonNumerator_le_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonSupport.lean)
-/
@[path]
private lemma abs_gaugeWilsonNumerator_le_partition_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E} :
-- imply
  |gaugeWilsonNumerator incidence K L| ≤ gaugePartition incidence K := by
-- proof
  apply StatMech.FrontierA.abs_gaugeWilsonNumerator_le_partition incidence K L

/--
[abs_gaugeWilsonExpectation_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonSupport.lean)
-/
@[path]
private lemma abs_gaugeWilsonExpectation_le_one_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E} :
-- imply
  |gaugeWilsonExpectation incidence K L| ≤ 1 := by
-- proof
  apply StatMech.FrontierA.abs_gaugeWilsonExpectation_le_one incidence K L

/--
[gaugeWilsonSurfaceSum_pos_iff_exists_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonSupport.lean)
-/
@[path]
private lemma gaugeWilsonSurfaceSum_pos_iff_exists_boundary_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  0 < gaugeWilsonSurfaceSum incidence K L ↔ ∃ A : Finset P, HasWilsonBoundary incidence A L := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonSurfaceSum_pos_iff_exists_boundary incidence K hK L

/--
[gaugeWilsonExpectation_pos_iff_exists_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonSupport.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_pos_iff_exists_boundary_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  0 < gaugeWilsonExpectation incidence K L ↔ ∃ A : Finset P, HasWilsonBoundary incidence A L := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_pos_iff_exists_boundary incidence K hK L

/--
[gaugeWilsonExpectation_eq_zero_iff_no_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonSupport.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_eq_zero_iff_no_boundary_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  gaugeWilsonExpectation incidence K L = 0 ↔ ¬ ∃ A : Finset P, HasWilsonBoundary incidence A L := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_eq_zero_iff_no_boundary incidence K hK L

/--
[gaugeWilsonExpectation_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonSupport.lean)
-/
@[path]
private lemma gaugeWilsonExpectation_mem_Icc_eq
  [Fintype E]
  [DecidableEq E]
  {incidence : P → Finset E}
  {K : P → ℝ}
  {L : Finset E}
-- given
  (hK : ∀ p, 0 < K p) :
-- imply
  gaugeWilsonExpectation incidence K L ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.FrontierA.gaugeWilsonExpectation_mem_Icc incidence K hK L


-- created on 2026-10-23

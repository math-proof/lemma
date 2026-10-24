import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectNoLoopNormalization
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[fkRectCriticalZeroTurnAtMostMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma fkRectCriticalZeroTurnAtMostMass_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 0 < q) :
-- imply
  0 ≤ fkRectCriticalZeroTurnAtMostMass R q L := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalZeroTurnAtMostMass_nonneg R hq L

/--
[fkRectCriticalZeroTurnAtMostMass_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma fkRectCriticalZeroTurnAtMostMass_le_one_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalZeroTurnAtMostMass R q L ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalZeroTurnAtMostMass_le_one R hq L

/--
[fkRectCriticalZeroTurnAboveMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma fkRectCriticalZeroTurnAboveMass_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 0 < q) :
-- imply
  0 ≤ fkRectCriticalZeroTurnAboveMass R q L := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalZeroTurnAboveMass_nonneg R hq L

/--
[fkRectCriticalZeroTurnExpectation_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma fkRectCriticalZeroTurnExpectation_nonneg_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  0 ≤ fkRectCriticalZeroTurnExpectation R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalZeroTurnExpectation_nonneg R hq

/--
[zeroTurnAboveMass_mul_succ_le_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma zeroTurnAboveMass_mul_succ_le_expectation_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 0 < q) :
-- imply
  ((L + 1 : Nat) : Real) * fkRectCriticalZeroTurnAboveMass R q L ≤ fkRectCriticalZeroTurnExpectation R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnAboveMass_mul_succ_le_expectation R hq L

/--
[aboveMass_le_half_of_expectation_le_half_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma aboveMass_le_half_of_expectation_le_half_succ_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 0 < q)
  (hmoment : fkRectCriticalZeroTurnExpectation R q ≤ ((L + 1 : Nat) : Real) / 2) :
-- imply
  fkRectCriticalZeroTurnAboveMass R q L ≤ (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierD.aboveMass_le_half_of_expectation_le_half_succ R hq L hmoment

/--
[fkRectCriticalZeroTurnAtMostMass_add_aboveMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma fkRectCriticalZeroTurnAtMostMass_add_aboveMass_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalZeroTurnAtMostMass R q L + fkRectCriticalZeroTurnAboveMass R q L = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalZeroTurnAtMostMass_add_aboveMass R hq L

/--
[half_le_fkRectCriticalZeroTurnAtMostMass_of_aboveMass_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma half_le_fkRectCriticalZeroTurnAtMostMass_of_aboveMass_le_half_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 0 < q)
  (htail : fkRectCriticalZeroTurnAboveMass R q L ≤ (1 : Real) / 2) :
-- imply
  (1 : Real) / 2 ≤ fkRectCriticalZeroTurnAtMostMass R q L := by
-- proof
  apply StatMech.FrontierD.half_le_fkRectCriticalZeroTurnAtMostMass_of_aboveMass_le_half R hq L htail

/--
[zeroTurnResidual_lower_of_count_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma zeroTurnResidual_lower_of_count_le_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
  {L : Nat}
-- given
  (hq : 4 < q)
  (hcount : fkRectZeroTurnLoopCount R omega ≤ L) :
-- imply
  (2 / Real.sqrt q) ^ L / q ≤ fkRectZeroTurnEulerResidual R q omega := by
-- proof
  apply StatMech.FrontierD.zeroTurnResidual_lower_of_count_le R hq omega hcount

/--
[zeroTurnCost_mul_atMostMass_le_allSectorNormalization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma zeroTurnCost_mul_atMostMass_le_allSectorNormalization_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 4 < q) :
-- imply
  ((2 / Real.sqrt q) ^ L / q) * fkRectCriticalZeroTurnAtMostMass R q L ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_mul_atMostMass_le_allSectorNormalization R hq L

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 4 < q)
  (hmass : (1 : Real) / 2 ≤ fkRectCriticalZeroTurnAtMostMass R q L) :
-- imply
  (2 / Real.sqrt q) ^ L / (2 * q) ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization R hq L hmass

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 4 < q)
  (htail : fkRectCriticalZeroTurnAboveMass R q L ≤ (1 : Real) / 2) :
-- imply
  (2 / Real.sqrt q) ^ L / (2 * q) ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_aboveMass_le_half R hq L htail

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_expectation_eq
  {R : FKRectTorus}
  {q : Real}
  {L : Nat}
-- given
  (hq : 4 < q)
  (hmoment : fkRectCriticalZeroTurnExpectation R q ≤ ((L + 1 : Nat) : Real) / 2) :
-- imply
  (2 / Real.sqrt q) ^ L / (2 * q) ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_expectation R hq L hmoment

/--
[tendsto_allSectorNormalization_negLog_div_height_zero_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma tendsto_allSectorNormalization_negLog_div_height_zero_of_lower_eq
  {R : Nat → FKRectTorus}
  {q : Real}
  {lower : Nat → Real}
-- given
  (hq : 4 < q)
  (hlowerPos : ∀ n, 0 < lower n)
  (hlower : ∀ n, lower n ≤ fkRectAllSectorNormalization (R n) q)
  (hlowerCost : Tendsto (fun n => -Real.log (lower n) / (R n).height) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => -Real.log (fkRectAllSectorNormalization (R n) q) / (R n).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_allSectorNormalization_negLog_div_height_zero_of_lower R hq lower hlowerPos hlower hlowerCost

/--
[tendsto_allSectorNormalization_negLog_div_height_zero_of_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma tendsto_allSectorNormalization_negLog_div_height_zero_of_expectation_eq
  {R : Nat → FKRectTorus}
  {q : Real}
  {L : Nat → Nat}
-- given
  (hq : 4 < q)
  (hmoment : ∀ n, fkRectCriticalZeroTurnExpectation (R n) q ≤ ((L n + 1 : Nat) : Real) / 2)
  (hcost : Tendsto (fun n => -Real.log ((2 / Real.sqrt q) ^ L n / (2 * q)) / (R n).height) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => -Real.log (fkRectAllSectorNormalization (R n) q) / (R n).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_allSectorNormalization_negLog_div_height_zero_of_expectation R hq L hmoment hcost

/--
[tendsto_allSectorNormalization_negLog_div_height_zero_of_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma tendsto_allSectorNormalization_negLog_div_height_zero_of_tail_eq
  {R : Nat → FKRectTorus}
  {q : Real}
  {L : Nat → Nat}
-- given
  (hq : 4 < q)
  (htail : ∀ n, fkRectCriticalZeroTurnAboveMass (R n) q (L n) ≤ (1 : Real) / 2)
  (hcost : Tendsto (fun n ↦ -Real.log ((2 / Real.sqrt q) ^ L n / (2 * q)) / (R n).height) atTop (nhds 0)) :
-- imply
  Tendsto (fun n ↦ -Real.log (fkRectAllSectorNormalization (R n) q) / (R n).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_allSectorNormalization_negLog_div_height_zero_of_tail R hq L htail hcost

/--
[tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_expectation_eq
  {R : Nat → FKRectTorus}
  {q : Real}
  {L : Nat → Nat}
-- given
  (hq : 4 < q)
  (hmoment : ∀ n, fkRectCriticalZeroTurnExpectation (R n) q ≤ ((L n + 1 : Nat) : Real) / 2)
  (hL : Tendsto (fun n => (L n : Real) / (R n).height) atTop (nhds 0))
  (hheight : Tendsto (fun n => (R n).height) atTop atTop) :
-- imply
  Tendsto (fun n => -Real.log (fkRectAllSectorNormalization (R n) q) / (R n).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_expectation R hq L hmoment hL hheight

/--
[tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectNoLoopNormalization.lean)
-/
@[path]
private lemma tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_tail_eq
  {R : Nat → FKRectTorus}
  {q : Real}
  {L : Nat → Nat}
-- given
  (hq : 4 < q)
  (htail : ∀ n, fkRectCriticalZeroTurnAboveMass (R n) q (L n) ≤ (1 : Real) / 2)
  (hL : Tendsto (fun n ↦ (L n : Real) / (R n).height) atTop (nhds 0))
  (hheight : Tendsto (fun n ↦ (R n).height) atTop atTop) :
-- imply
  Tendsto (fun n ↦ -Real.log (fkRectAllSectorNormalization (R n) q) / (R n).height) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_allSectorNormalization_negLog_div_height_zero_of_sublinear_tail R hq L htail hL hheight


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.DecoupledTwoPointClose
open Real Set StatMech StatMech.Probability


/--
[dtpc_witness_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DecoupledTwoPointClose.lean)
-/
@[path]
private lemma dtpc_witness_lhs_eq :
-- imply
  ((1 - (9 / 10 : ℝ)) * 1 + (9 / 10) * 0) ^ 2 + (1 / 2 : ℝ) ^ 2 * ((9 / 10) * (1 - 9 / 10)) * (1 - 0) ^ 2 = 13 / 400 := by
-- proof
  apply StatMech.Probability.dtpc_witness_lhs

/--
[dtpc_witness_rhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DecoupledTwoPointClose.lean)
-/
@[path]
private lemma dtpc_witness_rhs_eq :
-- imply
  ((1 - (9 / 10 : ℝ)) * |(1 : ℝ)| ^ (1 + (1 / 2 : ℝ) ^ 2) + (9 / 10) * |(0 : ℝ)| ^ (1 + (1 / 2 : ℝ) ^ 2)) ^ (2 / (1 + (1 / 2 : ℝ) ^ 2)) = ((1 : ℝ) / 10) ^ ((8 : ℝ) / 5) := by
-- proof
  apply StatMech.Probability.dtpc_witness_rhs

/--
[dtpc_witness_rhs_lt_lhs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DecoupledTwoPointClose.lean)
-/
@[path]
private lemma dtpc_witness_rhs_lt_lhs_eq :
-- imply
  ((1 : ℝ) / 10) ^ ((8 : ℝ) / 5) < 13 / 400 := by
-- proof
  apply StatMech.Probability.dtpc_witness_rhs_lt_lhs

/--
[dtpc_pbiasedHCLib_nine_tenths_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DecoupledTwoPointClose.lean)
-/
@[path]
private lemma dtpc_pbiasedHCLib_nine_tenths_false_eq :
-- imply
  ¬ PBiasedHCLib (9 / 10) := by
-- proof
  apply StatMech.Probability.dtpc_pbiasedHCLib_nine_tenths_false

/--
[dtpc_remainingGoal_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DecoupledTwoPointClose.lean)
-/
@[path]
private lemma dtpc_remainingGoal_false_eq
  {q : ℝ}
-- given
  (hq : (9 : ℝ) / 10 < q) :
-- imply
  ¬ stw_RemainingGoal q := by
-- proof
  apply StatMech.Probability.dtpc_remainingGoal_false hq

/--
[dtpc_coupled_true_at_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/DecoupledTwoPointClose.lean)
-/
@[path]
private lemma dtpc_coupled_true_at_witness_eq :
-- imply
  ((1 - (9 / 10 : ℝ)) * 1 + (9 / 10) * 0) ^ 2 + (1 / 2 : ℝ) ^ 2 * (2 * (9 / 10) * (1 - 9 / 10)) ^ 2 * (1 - 0) ^ 2 ≤ ((1 : ℝ) / 10) ^ ((8 : ℝ) / 5) := by
-- proof
  apply StatMech.Probability.dtpc_coupled_true_at_witness


-- created on 2026-10-23

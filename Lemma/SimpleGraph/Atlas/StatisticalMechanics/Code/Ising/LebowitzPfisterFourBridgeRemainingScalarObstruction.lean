import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeRemainingScalarObstruction.Part2
open StatMech StatMech.Ising


/--
[fourBridgeRemainingCounterexample_mem_establishedAggregateRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRemainingScalarObstruction.lean)
-/
@[path]
private lemma fourBridgeRemainingCounterexample_mem_establishedAggregateRegion_eq :
-- imply
  FourBridgeEstablishedAggregateRegion fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD := by
-- proof
  apply StatMech.Ising.fourBridgeRemainingCounterexample_mem_establishedAggregateRegion

/--
[fourBridgeRemainingCounterexample_closed_coefficients_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRemainingScalarObstruction.lean)
-/
@[path]
private lemma fourBridgeRemainingCounterexample_closed_coefficients_nonpos_eq :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 0 <= 0 ∧ fourBridgeVarianceSkewBernsteinCoeff fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 1 <= 0 ∧ fourBridgeVarianceSkewBernsteinCoeff fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 2 <= 0 ∧ fourBridgeVarianceSkewBernsteinCoeff fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 5 <= 0 ∧ fourBridgeVarianceSkewBernsteinCoeff fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 6 <= 0 := by
-- proof
  apply StatMech.Ising.fourBridgeRemainingCounterexample_closed_coefficients_nonpos

/--
[fourBridgeRemainingCounterexample_middle_three_four_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRemainingScalarObstruction.lean)
-/
@[path]
private lemma fourBridgeRemainingCounterexample_middle_three_four_pos_eq :
-- imply
  0 < fourBridgeVarianceSkewBernsteinCoeff fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 3 ∧ 0 < fourBridgeVarianceSkewBernsteinCoeff fourBridgeRemainingCounterexampleA fourBridgeRemainingCounterexampleB fourBridgeRemainingCounterexampleC fourBridgeRemainingCounterexampleD 4 := by
-- proof
  apply StatMech.Ising.fourBridgeRemainingCounterexample_middle_three_four_pos

/--
[fourBridgeSkewCounterexample_mem_establishedAggregateRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRemainingScalarObstruction.lean)
-/
@[path]
private lemma fourBridgeSkewCounterexample_mem_establishedAggregateRegion_eq :
-- imply
  FourBridgeEstablishedAggregateRegion fourBridgeSkewCounterexampleA fourBridgeSkewCounterexampleB fourBridgeSkewCounterexampleC fourBridgeSkewCounterexampleD := by
-- proof
  apply StatMech.Ising.fourBridgeSkewCounterexample_mem_establishedAggregateRegion

/--
[fourBridgeSkewCounterexample_polynomial_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeRemainingScalarObstruction.lean)
-/
@[path]
private lemma fourBridgeSkewCounterexample_polynomial_pos_eq :
-- imply
  0 < fourBridgeVarianceSkewPolynomial (9 / 10) fourBridgeSkewCounterexampleA fourBridgeSkewCounterexampleB fourBridgeSkewCounterexampleC fourBridgeSkewCounterexampleD := by
-- proof
  apply StatMech.Ising.fourBridgeSkewCounterexample_polynomial_pos


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeCounterexampleGHS
open StatMech StatMech.Ising


/--
[fourBridgeSecondMiddleCutCounterexample_violates_ghsZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeCounterexampleGHS.lean)
-/
@[path]
private lemma fourBridgeSecondMiddleCutCounterexample_violates_ghsZero_eq :
-- imply
  0 < fourBridgeSecondMiddleCutCounterexampleA ^ 3 - 3 * fourBridgeSecondMiddleCutCounterexampleA * fourBridgeSecondMiddleCutCounterexampleB - fourBridgeSecondMiddleCutCounterexampleA + 3 * fourBridgeSecondMiddleCutCounterexampleC := by
-- proof
  apply StatMech.Ising.fourBridgeSecondMiddleCutCounterexample_violates_ghsZero

/--
[fourBridgePointwiseCutCounterexample_violates_ghsZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFourBridgeCounterexampleGHS.lean)
-/
@[path]
private lemma fourBridgePointwiseCutCounterexample_violates_ghsZero_eq :
-- imply
  0 < fourBridgePointwiseCutCounterexampleA ^ 3 - 3 * fourBridgePointwiseCutCounterexampleA * fourBridgePointwiseCutCounterexampleB - fourBridgePointwiseCutCounterexampleA + 3 * fourBridgePointwiseCutCounterexampleC := by
-- proof
  apply StatMech.Ising.fourBridgePointwiseCutCounterexample_violates_ghsZero


-- created on 2026-10-23

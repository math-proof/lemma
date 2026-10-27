import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSymmetricMeanSwitching.Part2
open Filter Set Topology StatMech StatMech.FrontierA


/--
[finiteExpVarianceSkew_nonpos_of_switchingPairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean)
-/
@[path]
private lemma finiteExpVarianceSkew_nonpos_of_switchingPairing_eq
  [Fintype E]
  {r : Real}
-- given
  (w I : E -> Real)
  (hpair : FiniteExpVarianceSkewSwitchingPairing w I r) :
-- imply
  finiteExpVarianceSkew w I r <= 0 := by
-- proof
  apply StatMech.FrontierA.finiteExpVarianceSkew_nonpos_of_switchingPairing w I r hpair

/--
[oddPrismTransferBridgeVarianceSkewNumerator_nonpos_of_switchingPairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVarianceSkewNumerator_nonpos_of_switchingPairing_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hpair : OddPrismTransferSkewSwitchingPairing beta n r) :
-- imply
  oddPrismTransferBridgeVarianceSkewNumerator beta n r <= 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVarianceSkewNumerator_nonpos_of_switchingPairing beta n r hpair

/--
[oddPrismTransferBridgeVariance_le_neg_of_switchingPairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_le_neg_of_switchingPairing_eq
  {beta : Real}
  {n : Nat}
  {r : Real}
-- given
  (hn : 0 < n)
  (hpair : OddPrismTransferSkewSwitchingPairing beta n r) :
-- imply
  oddPrismTransferBridgeVariance beta n r <= oddPrismTransferBridgeVariance beta n (-r) := by
-- proof
  apply StatMech.FrontierA.oddPrismTransferBridgeVariance_le_neg_of_switchingPairing beta n hn r hpair

/--
[oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder_Icc_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hvar : forall t, 0 <= t -> t <= beta -> unequalReplicaBridgeVariance (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) beta (fun v => beta * oddPrismPlusField n v.1) (fun v => beta * oddPrismPlusField n v.1) t <= unequalReplicaBridgeVariance (oddPrismLowerBlockGraph n) (oddPrismUpperBlockGraph n) (oddPrismUnequalGlueGraph n) beta (fun v => beta * oddPrismPlusField n v.1) (fun v => beta * oddPrismPlusField n v.1) (-t)) :
-- imply
  OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeSymmetricMeanOrder_of_varianceOrder_Icc hbeta hvar

/--
[oddPrismUnequalBridgeSymmetricMeanOrder_of_transferSwitchingPairings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeSymmetricMeanOrder_of_transferSwitchingPairings_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n)
  (hpair : forall t, 0 <= t -> t <= beta -> OddPrismTransferSkewSwitchingPairing beta n t) :
-- imply
  OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeSymmetricMeanOrder_of_transferSwitchingPairings hbeta hn hpair

/--
[oddPrismUnequalBridgeSymmetricMeanOrder_all_of_transferSwitchingPairings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeSymmetricMeanOrder_all_of_transferSwitchingPairings_eq
  {beta : Real}
-- given
  (hbeta : 0 <= beta)
  (hpair : forall n, 0 < n -> forall t, 0 <= t -> t <= beta -> OddPrismTransferSkewSwitchingPairing beta n t) :
-- imply
  forall n, OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeSymmetricMeanOrder_all_of_transferSwitchingPairings hbeta hpair

/--
[oddPrismUnequalBridgeSymmetricMeanOrder_of_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSymmetricMeanSwitching.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeSymmetricMeanOrder_of_nonpos_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : beta <= 0) :
-- imply
  OddPrismUnequalBridgeSymmetricMeanOrder beta n := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeSymmetricMeanOrder_of_nonpos hbeta n


-- created on 2026-10-23

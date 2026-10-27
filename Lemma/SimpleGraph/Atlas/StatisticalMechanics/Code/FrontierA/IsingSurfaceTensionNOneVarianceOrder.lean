import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneVarianceOrder
open StatMech StatMech.FrontierA StatMech.FrontierA.NOneSymmetricMeanCertificate


/--
[oddPrismTransferBridgeVarianceSkewNumerator_one_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneVarianceOrder.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVarianceSkewNumerator_one_nonpos_eq
  {beta r : Real}
-- given
  (hbeta : 0 ≤ beta)
  (hr : 0 ≤ r) :
-- imply
  oddPrismTransferBridgeVarianceSkewNumerator beta 1 r ≤ 0 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeVarianceSkewNumerator_one_nonpos beta r hbeta hr

/--
[oddPrismTransferBridgeVariance_one_le_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneVarianceOrder.lean)
-/
@[path]
private lemma oddPrismTransferBridgeVariance_one_le_neg_eq
  {beta r : Real}
-- given
  (hbeta : 0 ≤ beta)
  (hr : 0 ≤ r) :
-- imply
  oddPrismTransferBridgeVariance beta 1 r ≤ oddPrismTransferBridgeVariance beta 1 (-r) := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismTransferBridgeVariance_one_le_neg beta r hbeta hr

/--
[oddPrismUnequalBridgeSymmetricMeanOrder_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneVarianceOrder.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeSymmetricMeanOrder_one_eq
  {beta : Real}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  OddPrismUnequalBridgeSymmetricMeanOrder beta 1 := by
-- proof
  apply StatMech.FrontierA.NOneSymmetricMeanCertificate.oddPrismUnequalBridgeSymmetricMeanOrder_one beta hbeta


-- created on 2026-10-23

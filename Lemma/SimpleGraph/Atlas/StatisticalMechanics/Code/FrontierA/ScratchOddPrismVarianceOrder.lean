import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.ScratchOddPrismVarianceOrder.Part2
open StatMech StatMech.FrontierA


/--
[fis_interface_eq_empty_of_isEmpty_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ScratchOddPrismVarianceOrder.lean)
-/
@[path]
private lemma fis_interface_eq_empty_of_isEmpty_right_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [IsEmpty W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
-- given
  (hci : StatMech.FK.fis_CrossInterface G H K) :
-- imply
  StatMech.FK.fis_interface G H K = ∅ := by
-- proof
  apply StatMech.FrontierA.fis_interface_eq_empty_of_isEmpty_right G H K hci

/--
[unequalReplicaBridgeVariance_eq_zero_of_isEmpty_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ScratchOddPrismVarianceOrder.lean)
-/
@[path]
private lemma unequalReplicaBridgeVariance_eq_zero_of_isEmpty_right_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype W]
  [DecidableEq W]
  [IsEmpty W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)}
  [DecidableRel K.Adj]
  {J : Real}
  {r : Real}
-- given
  (hci : StatMech.FK.fis_CrossInterface G H K)
  (hf : V -> Real)
  (hg : W -> Real) :
-- imply
  unequalReplicaBridgeVariance G H K J hf hg r = 0 := by
-- proof
  apply StatMech.FrontierA.unequalReplicaBridgeVariance_eq_zero_of_isEmpty_right G H K hci J hf hg r

/--
[oddPrismUnequalBridgeVariance_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ScratchOddPrismVarianceOrder.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeVariance_zero_eq
  {beta r : Real} :
-- imply
  unequalReplicaBridgeVariance (oddPrismLowerBlockGraph 0) (oddPrismUpperBlockGraph 0) (oddPrismUnequalGlueGraph 0) beta (fun v => beta * oddPrismPlusField 0 v.1) (fun v => beta * oddPrismPlusField 0 v.1) r = 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeVariance_zero beta r

/--
[oddPrismUnequalBridgeVarianceOrder_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ScratchOddPrismVarianceOrder.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeVarianceOrder_zero_eq
  {beta : Real} :
-- imply
  OddPrismUnequalBridgeVarianceOrder beta 0 := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeVarianceOrder_zero beta

/--
[oddPrismUnequalBridgeVarianceOrder_iff_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/ScratchOddPrismVarianceOrder.lean)
-/
@[path]
private lemma oddPrismUnequalBridgeVarianceOrder_iff_transfer_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  OddPrismUnequalBridgeVarianceOrder beta n ↔ ∀ t, 0 <= t -> oddPrismTransferBridgeVariance beta n t <= oddPrismTransferBridgeVariance beta n (-t) := by
-- proof
  apply StatMech.FrontierA.oddPrismUnequalBridgeVarianceOrder_iff_transfer beta n hn


-- created on 2026-10-23

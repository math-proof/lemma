import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexFullComponentMaskSwap
open Finset StatMech StatMech.FrontierD


/--
[SixVertexFullDisagreementMask.local_eq_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma local_eq_disagreement_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask)
  (hactive : exists d, sixVertexTorusLocalSwitchMask mask v d = true) :
-- imply
  forall r, sixVertexTorusLocalSwitchMask mask v r = decide (sixVertexLocalIncomingPattern omega v r ≠ sixVertexLocalIncomingPattern eta v r) := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.local_eq_disagreement hmask v hactive

/--
[SixVertexFullDisagreementMask.local_eq_or_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma local_eq_or_swap_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask) :
-- imply
  (sixVertexLocalIncomingPattern (sixVertexTorusSwitchFirst mask omega eta) v, sixVertexLocalIncomingPattern (sixVertexTorusSwitchSecond mask omega eta) v) = (sixVertexLocalIncomingPattern omega v, sixVertexLocalIncomingPattern eta v) \/ (sixVertexLocalIncomingPattern (sixVertexTorusSwitchFirst mask omega eta) v, sixVertexLocalIncomingPattern (sixVertexTorusSwitchSecond mask omega eta) v) = (sixVertexLocalIncomingPattern eta v, sixVertexLocalIncomingPattern omega v) := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.local_eq_or_swap hmask v

/--
[SixVertexFullDisagreementMask.localCTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma localCTypeCount_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask) :
-- imply
  sixVertexLocalCTypeCount (sixVertexLocalIncomingPattern (sixVertexTorusSwitchFirst mask omega eta) v) (sixVertexLocalIncomingPattern (sixVertexTorusSwitchSecond mask omega eta) v) = sixVertexLocalCTypeCount (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v) := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.localCTypeCount hmask v

/--
[SixVertexFullDisagreementMask.boundedFineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma boundedFineRowProfile_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile ((sixVertexTorusSwitchFirst mask omega eta).horizontal, (sixVertexTorusSwitchSecond mask omega eta).horizontal) = sixVertexHorizontalPairBoundedFineRowProfile (omega.horizontal, eta.horizontal) := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.boundedFineRowProfile hmask

/--
[sixVertexSeedDisagreementComponentMask_selects_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma sixVertexSeedDisagreementComponentMask_selects_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed e : SixVertexTorusEdge T} :
-- imply
  sixVertexTorusMaskSelects (sixVertexSeedDisagreementComponentMask omega eta seed) e = true <-> (sixVertexTorusDisagreementGraph omega eta).Reachable seed e := by
-- proof
  apply StatMech.FrontierD.sixVertexSeedDisagreementComponentMask_selects_iff omega eta seed e

/--
[sixVertexSeedDisagreementComponentMask_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma sixVertexSeedDisagreementComponentMask_full_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexTorusEdge T}
-- given
  (hseed : sixVertexTorusEdgeDisagrees omega eta seed) :
-- imply
  SixVertexFullDisagreementMask omega eta (sixVertexSeedDisagreementComponentMask omega eta seed) := by
-- proof
  apply StatMech.FrontierD.sixVertexSeedDisagreementComponentMask_full omega eta seed hseed

/--
[SixVertexFullDisagreementMask.vertexMask_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma vertexMask_bondMate_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
  {d : SixVertexTorusDart T}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask)
  (hdisagrees : sixVertexTorusEdgeDisagrees omega eta (sixVertexTorusDartEdge T d)) :
-- imply
  sixVertexFullDisagreementVertexMask mask d.1 = sixVertexFullDisagreementVertexMask mask (sixVertexTorusDartBondMate T d).1 := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.vertexMask_bondMate hmask d hdisagrees

/--
[SixVertexFullDisagreementMask.vertexMask_eq_localMask_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma vertexMask_eq_localMask_of_disagrees_eq
  {T : EvenTorus}
  {omega eta mask : SixVertexArrows T}
  {d : SixVertexTorusDart T}
-- given
  (hmask : SixVertexFullDisagreementMask omega eta mask)
  (hdisagrees : sixVertexTorusEdgeDisagrees omega eta (sixVertexTorusDartEdge T d)) :
-- imply
  sixVertexFullDisagreementVertexMask mask d.1 = sixVertexTorusLocalSwitchMask mask d.1 d.2 := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.vertexMask_eq_localMask_of_disagrees hmask d hdisagrees

/--
[SixVertexFullDisagreementMask.fullSwapBondCoherent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma fullSwapBondCoherent_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask) :
-- imply
  FKColoredFullSwapBondCoherent source (sixVertexFullDisagreementVertexMask mask) := by
-- proof
  apply StatMech.FrontierD.SixVertexFullDisagreementMask.fullSwapBondCoherent source mask hmask

/--
[sixVertexFullDisagreementColoredTarget_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma sixVertexFullDisagreementColoredTarget_arrows_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
  {layer : Bool}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask) :
-- imply
  (sixVertexFullDisagreementColoredTarget source mask hmask layer).arrows = if layer then sixVertexTorusSwitchSecond mask (source false).arrows (source true).arrows else sixVertexTorusSwitchFirst mask (source false).arrows (source true).arrows := by
-- proof
  apply StatMech.FrontierD.sixVertexFullDisagreementColoredTarget_arrows source mask hmask layer

/--
[sixVertexFullDisagreementColoredTarget_boundedFineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma sixVertexFullDisagreementColoredTarget_boundedFineRowProfile_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile ((sixVertexFullDisagreementColoredTarget source mask hmask false).arrows.horizontal, (sixVertexFullDisagreementColoredTarget source mask hmask true).arrows.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile ((source false).arrows.horizontal, (source true).arrows.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexFullDisagreementColoredTarget_boundedFineRowProfile source mask hmask

/--
[sixVertexFullDisagreementColoredTarget_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma sixVertexFullDisagreementColoredTarget_bigrade_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask) :
-- imply
  (fkColoredLoopPairingPairTotalC (sixVertexFullDisagreementColoredTarget source mask hmask), fkColoredTrueStrandSlotCount (sixVertexFullDisagreementColoredTarget source mask hmask)) = (fkColoredLoopPairingPairTotalC source, fkColoredTrueStrandSlotCount source) := by
-- proof
  apply StatMech.FrontierD.sixVertexFullDisagreementColoredTarget_bigrade source mask hmask

/--
[sixVertexFullDisagreementColoredTarget_middleSectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma sixVertexFullDisagreementColoredTarget_middleSectors_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {mask : SixVertexArrows T}
  {middle : Nat}
-- given
  (hmask : SixVertexFullDisagreementMask (source false).arrows (source true).arrows mask)
  (hlower : sixVertexUpCount (svTorusVerticalRows T (source false).arrows (svFinLast T.height_pos)) = middle - 1)
  (hupper : sixVertexUpCount (svTorusVerticalRows T (source true).arrows (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (source false).arrows (source true).arrows = 1) :
-- imply
  sixVertexUpCount (svTorusVerticalRows T (sixVertexFullDisagreementColoredTarget source mask hmask false).arrows (svFinLast T.height_pos)) = middle /\ sixVertexUpCount (svTorusVerticalRows T (sixVertexFullDisagreementColoredTarget source mask hmask true).arrows (svFinLast T.height_pos)) = middle := by
-- proof
  apply StatMech.FrontierD.sixVertexFullDisagreementColoredTarget_middleSectors source mask hmask middle hlower hupper hmiddle htransfer

/--
[sixVertexLoopDecoratedFullMaskTarget_colored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedFullMaskTarget_colored_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt)}
  {mask : SixVertexArrows T}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmask : SixVertexFullDisagreementMask (sixVertexLoopDecoratedPairColored source false).arrows (sixVertexLoopDecoratedPairColored source true).arrows mask)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (sixVertexLoopDecoratedPairColored source false).arrows (sixVertexLoopDecoratedPairColored source true).arrows = 1) :
-- imply
  sixVertexLoopDecoratedPairColored (sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos hmiddle_lt source mask hmask htransfer) = sixVertexFullDisagreementColoredTarget (sixVertexLoopDecoratedPairColored source) mask hmask := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedFullMaskTarget_colored middle hmiddle_pos hmiddle_lt source mask hmask htransfer

/--
[sixVertexLoopDecoratedFullMaskTarget_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFullComponentMaskSwap.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedFullMaskTarget_bigrade_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt)}
  {mask : SixVertexArrows T}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmask : SixVertexFullDisagreementMask (sixVertexLoopDecoratedPairColored source false).arrows (sixVertexLoopDecoratedPairColored source true).arrows mask)
  (htransfer : sixVertexTorusMaskSeamTransfer mask (sixVertexLoopDecoratedPairColored source false).arrows (sixVertexLoopDecoratedPairColored source true).arrows = 1) :
-- imply
  sixVertexLoopDecoratedPairBigrade (sixVertexLoopDecoratedFullMaskTarget middle hmiddle_pos hmiddle_lt source mask hmask htransfer) = sixVertexLoopDecoratedPairBigrade source := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedFullMaskTarget_bigrade middle hmiddle_pos hmiddle_lt source mask hmask htransfer


-- created on 2026-10-23

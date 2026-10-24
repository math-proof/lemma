import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexSpliceKeyLayerSwap
open StatMech StatMech.FrontierD StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey


/--
[fkColoredLoopPairingPairSwapLayers_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma fkColoredLoopPairingPairSwapLayers_apply_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool} :
-- imply
  fkColoredLoopPairingPairSwapLayers source layer = source (!layer) := by
-- proof
  apply StatMech.FrontierD.fkColoredLoopPairingPairSwapLayers_apply source layer

/--
[fkColoredLoopPairingPairSwapLayers_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma fkColoredLoopPairingPairSwapLayers_swap_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T} :
-- imply
  fkColoredLoopPairingPairSwapLayers (fkColoredLoopPairingPairSwapLayers source) = source := by
-- proof
  apply StatMech.FrontierD.fkColoredLoopPairingPairSwapLayers_swap source

/--
[fkColoredLoopPairingPairSwapLayers_slotColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma fkColoredLoopPairingPairSwapLayers_slotColor_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {slot : FKLayeredStrandSlot T} :
-- imply
  fkColoredLayeredSlotColor (fkColoredLoopPairingPairSwapLayers source) slot = fkColoredLayeredSlotColor source (fkColoredLayeredStrandSlotSwapLayers slot) := by
-- proof
  apply StatMech.FrontierD.fkColoredLoopPairingPairSwapLayers_slotColor source slot

/--
[fkColoredLoopPairingPairSwapLayers_trueStrandSlotCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma fkColoredLoopPairingPairSwapLayers_trueStrandSlotCount_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T} :
-- imply
  fkColoredTrueStrandSlotCount (fkColoredLoopPairingPairSwapLayers source) = fkColoredTrueStrandSlotCount source := by
-- proof
  apply StatMech.FrontierD.fkColoredLoopPairingPairSwapLayers_trueStrandSlotCount source

/--
[fkColoredLoopPairingPairSwapLayers_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma fkColoredLoopPairingPairSwapLayers_totalC_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T} :
-- imply
  fkColoredLoopPairingPairTotalC (fkColoredLoopPairingPairSwapLayers source) = fkColoredLoopPairingPairTotalC source := by
-- proof
  apply StatMech.FrontierD.fkColoredLoopPairingPairSwapLayers_totalC source

/--
[sixVertexPairAtMostTwoCycleRelated_swap_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma sixVertexPairAtMostTwoCycleRelated_swap_target_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hrelated : sixVertexPairAtMostTwoCycleRelated source target) :
-- imply
  sixVertexPairAtMostTwoCycleRelated source (target.2, target.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexPairAtMostTwoCycleRelated_swap_target hrelated

/--
[recovers_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma recovers_source_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey source} :
-- imply
  key.splice.symm.target = source := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey.recovers_source key

/--
[target_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma target_bigrade_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey source} :
-- imply
  (fkColoredLoopPairingPairTotalC key.splice.target, fkColoredTrueStrandSlotCount key.splice.target) = (fkColoredLoopPairingPairTotalC source, fkColoredTrueStrandSlotCount source) := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey.target_bigrade key

/--
[target_twoCycleFine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma target_twoCycleFine_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey source} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated ((source false).arrows, (source true).arrows) ((key.splice.target false).arrows, (key.splice.target true).arrows) := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey.target_twoCycleFine key

/--
[swapSplice_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma swapSplice_target_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey source} :
-- imply
  key.swapSplice.target = fkColoredLoopPairingPairSwapLayers key.splice.target := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey.swapSplice_target key

/--
[swapSplice_preservesTotalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma swapSplice_preservesTotalC_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey source} :
-- imply
  key.swapSplice.PreservesTotalC := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey.swapSplice_preservesTotalC key

/--
[swapSplice_seamDelta_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma swapSplice_seamDelta_false_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey source}
-- given
  (hsource : SourceSeamDifferenceTwo source) :
-- imply
  key.swapSplice.seamDelta false = 1 := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey.swapSplice_seamDelta_false key hsource

/--
[swapSplice_seamDelta_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma swapSplice_seamDelta_true_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey source}
-- given
  (hsource : SourceSeamDifferenceTwo source) :
-- imply
  key.swapSplice.seamDelta true = -1 := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey.swapSplice_seamDelta_true key hsource

/--
[swap_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma swap_target_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey source}
-- given
  (hsource : SourceSeamDifferenceTwo source) :
-- imply
  (key.swap hsource).splice.target = fkColoredLoopPairingPairSwapLayers key.splice.target := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey.swap_target key hsource

/--
[paired_target_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexSpliceKeyLayerSwap.lean)
-/
@[path]
private lemma paired_target_distinct_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferSpliceKey source}
-- given
  (hsource : SourceSeamDifferenceTwo source)
  (hlayers : key.splice.target false ≠ key.splice.target true) :
-- imply
  (key.paired hsource false).splice.target ≠ (key.paired hsource true).splice.target := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferSpliceKey.paired_target_distinct key hsource hlayers


-- created on 2026-10-23

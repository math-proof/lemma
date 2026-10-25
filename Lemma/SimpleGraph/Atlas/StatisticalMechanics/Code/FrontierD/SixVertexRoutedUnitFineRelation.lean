import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRoutedUnitFineRelation.Part4
open StatMech StatMech.FrontierD StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferRoutedKey


/--
[target_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean)
-/
@[path]
private lemma target_bigrade_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferRoutedKey source} :
-- imply
  (fkColoredLoopPairingPairTotalC key.splice.target, fkColoredTrueStrandSlotCount key.splice.target) = (fkColoredLoopPairingPairTotalC source, fkColoredTrueStrandSlotCount source) := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferRoutedKey.target_bigrade key

/--
[target_fine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean)
-/
@[path]
private lemma target_fine_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferRoutedKey source} :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile ((key.splice.target false).arrows.horizontal, (key.splice.target true).arrows.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile ((source false).arrows.horizontal, (source true).arrows.horizontal) := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferRoutedKey.target_fine key

/--
[target_twoCycleFine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean)
-/
@[path]
private lemma target_twoCycleFine_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {key : FKColoredFineTwoCycleUnitTransferRoutedKey source} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated ((source false).arrows, (source true).arrows) ((key.splice.target false).arrows, (key.splice.target true).arrows) := by
-- proof
  apply StatMech.FrontierD.FKColoredFineTwoCycleUnitTransferRoutedKey.target_twoCycleFine key

/--
[sixVertexLoopDecoratedRoutedUnitTarget_colored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedRoutedUnitTarget_colored_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt)}
  {key : FKColoredFineTwoCycleUnitTransferRoutedKey (sixVertexLoopDecoratedPairColored source)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  sixVertexLoopDecoratedPairColored (sixVertexLoopDecoratedRoutedUnitTarget middle hmiddle_pos hmiddle_lt source key) = key.splice.target := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedRoutedUnitTarget_colored middle hmiddle_pos hmiddle_lt source key

/--
[sixVertexLoopDecoratedRoutedUnitFineTarget_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedRoutedUnitFineTarget_bigrade_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {key : FKColoredFineTwoCycleUnitTransferRoutedKey (sixVertexLoopDecoratedPairColored source.1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  sixVertexLoopDecoratedPairBigrade (sixVertexLoopDecoratedRoutedUnitFineTarget middle hmiddle_pos hmiddle_lt profile source key).1 = sixVertexLoopDecoratedPairBigrade source.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedRoutedUnitFineTarget_bigrade middle hmiddle_pos hmiddle_lt profile source key

/--
[sixVertexLoopRoutedUnitFineRelated_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopRoutedUnitFineRelated_nonempty_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {key : FKColoredFineTwoCycleUnitTransferRoutedKey (sixVertexLoopDecoratedPairColored source.1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  (Finset.univ.filter (SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt profile source)).Nonempty := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopRoutedUnitFineRelated_nonempty middle hmiddle_pos hmiddle_lt profile source key

/--
[rawFineProfile_of_routedUnitRelationEdgeDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRoutedUnitFineRelation.lean)
-/
@[path]
private lemma rawFineProfile_of_routedUnitRelationEdgeDegree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile), Nonempty (FKColoredFineTwoCycleUnitTransferRoutedKey (sixVertexLoopDecoratedPairColored source.1)))
  (hdegree : forall profile source target, SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt profile source target -> (Finset.univ.filter fun otherSource => SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt profile otherSource target).card <= (Finset.univ.filter (SixVertexLoopRoutedUnitFineRelated middle hmiddle_pos hmiddle_lt profile source)).card) :
-- imply
  forall profile : SixVertexHorizontalBoundedFineRowProfile T, 0 <= sixVertexHorizontalFineRowProfileSignedSum T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle profile := by
-- proof
  apply StatMech.FrontierD.rawFineProfile_of_routedUnitRelationEdgeDegree middle hmiddle_pos hmiddle_lt hne hdegree


-- created on 2026-10-23

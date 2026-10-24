import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexResolvedUnitCrossFineRelation
open StatMech StatMech.FrontierD


/--
[fkColoredVertexCrossTarget_slotColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_slotColor_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {slot : FKLayeredStrandSlot T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  fkColoredLayeredSlotColor (fkColoredVertexCrossTarget source mask hbond) slot = fkColoredLayeredSlotColor source (fkColoredFullSwapLayeredSlotEquiv mask slot) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_slotColor source mask hbond slot

/--
[fkColoredVertexCrossTarget_trueStrandSlotCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_trueStrandSlotCount_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  fkColoredTrueStrandSlotCount (fkColoredVertexCrossTarget source mask hbond) = fkColoredTrueStrandSlotCount source := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_trueStrandSlotCount source mask hbond

/--
[fkColoredVertexCrossTarget_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_bigrade_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  (fkColoredLoopPairingPairTotalC (fkColoredVertexCrossTarget source mask hbond), fkColoredTrueStrandSlotCount (fkColoredVertexCrossTarget source mask hbond)) = (fkColoredLoopPairingPairTotalC source, fkColoredTrueStrandSlotCount source) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_bigrade source mask hbond

/--
[FKColoredResolvedUnitCross.target_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma target_bigrade_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {cross : FKColoredResolvedUnitCross source} :
-- imply
  (fkColoredLoopPairingPairTotalC cross.target, fkColoredTrueStrandSlotCount cross.target) = (fkColoredLoopPairingPairTotalC source, fkColoredTrueStrandSlotCount source) := by
-- proof
  apply StatMech.FrontierD.FKColoredResolvedUnitCross.target_bigrade cross

/--
[FKColoredResolvedUnitCross.target_fine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma target_fine_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {cross : FKColoredResolvedUnitCross source} :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile ((cross.target false).arrows.horizontal, (cross.target true).arrows.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile ((source false).arrows.horizontal, (source true).arrows.horizontal) := by
-- proof
  apply StatMech.FrontierD.FKColoredResolvedUnitCross.target_fine cross

/--
[FKColoredResolvedUnitCross.target_twoCycleFine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma target_twoCycleFine_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {cross : FKColoredResolvedUnitCross source} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated ((source false).arrows, (source true).arrows) ((cross.target false).arrows, (cross.target true).arrows) := by
-- proof
  apply StatMech.FrontierD.FKColoredResolvedUnitCross.target_twoCycleFine cross

/--
[sixVertexLoopDecoratedResolvedUnitCrossTarget_colored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedResolvedUnitCrossTarget_colored_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {source : SixVertexLoopDecoratedPair T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt)}
  {cross : FKColoredResolvedUnitCross (sixVertexLoopDecoratedPairColored source)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  sixVertexLoopDecoratedPairColored (sixVertexLoopDecoratedResolvedUnitCrossTarget middle hmiddle_pos hmiddle_lt source cross) = cross.target := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedResolvedUnitCrossTarget_colored middle hmiddle_pos hmiddle_lt source cross

/--
[sixVertexLoopDecoratedResolvedUnitCrossFineTarget_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedResolvedUnitCrossFineTarget_bigrade_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {cross : FKColoredResolvedUnitCross (sixVertexLoopDecoratedPairColored source.1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  sixVertexLoopDecoratedPairBigrade (sixVertexLoopDecoratedResolvedUnitCrossFineTarget middle hmiddle_pos hmiddle_lt profile source cross).1 = sixVertexLoopDecoratedPairBigrade source.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedResolvedUnitCrossFineTarget_bigrade middle hmiddle_pos hmiddle_lt profile source cross

/--
[sixVertexLoopResolvedUnitCrossFineRelated_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopResolvedUnitCrossFineRelated_nonempty_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {cross : FKColoredResolvedUnitCross (sixVertexLoopDecoratedPairColored source.1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  (Finset.univ.filter (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile source)).Nonempty := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopResolvedUnitCrossFineRelated_nonempty middle hmiddle_pos hmiddle_lt profile source cross

/--
[sixVertexLoopResolvedUnitCrossOfRelated_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopResolvedUnitCrossOfRelated_target_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  target = sixVertexLoopDecoratedResolvedUnitCrossFineTarget middle hmiddle_pos hmiddle_lt profile source (sixVertexLoopResolvedUnitCrossOfRelated middle hmiddle_pos hmiddle_lt profile source target hrelated) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopResolvedUnitCrossOfRelated_target middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[sixVertexLoopResolvedUnitCrossFineRelated_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopResolvedUnitCrossFineRelated_bigrade_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  sixVertexLoopDecoratedPairBigrade target.1 = sixVertexLoopDecoratedPairBigrade source.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopResolvedUnitCrossFineRelated_bigrade middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[sixVertexLoopResolvedUnitCrossFineRelated_twoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopResolvedUnitCrossFineRelated_twoCycle_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile source target) :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated ((sixVertexLoopDecoratedPairColored source.1 false).arrows, (sixVertexLoopDecoratedPairColored source.1 true).arrows) ((sixVertexLoopDecoratedPairColored target.1 false).arrows, (sixVertexLoopDecoratedPairColored target.1 true).arrows) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopResolvedUnitCrossFineRelated_twoCycle middle hmiddle_pos hmiddle_lt profile source target hrelated

/--
[rawFineProfile_of_resolvedUnitCrossRelationEdgeDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma rawFineProfile_of_resolvedUnitCrossRelationEdgeDegree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile), Nonempty (FKColoredResolvedUnitCross (sixVertexLoopDecoratedPairColored source.1)))
  (hdegree : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile), SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile source target -> (Finset.univ.filter fun otherSource => SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile otherSource target).card <= (Finset.univ.filter (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile source)).card) :
-- imply
  forall profile : SixVertexHorizontalBoundedFineRowProfile T, 0 <= sixVertexHorizontalFineRowProfileSignedSum T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle profile := by
-- proof
  apply StatMech.FrontierD.rawFineProfile_of_resolvedUnitCrossRelationEdgeDegree middle hmiddle_pos hmiddle_lt hne hdegree

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedUnitCrossRelationEdgeDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexResolvedUnitCrossFineRelation.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedUnitCrossRelationEdgeDegree_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hne : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile), Nonempty (FKColoredResolvedUnitCross (sixVertexLoopDecoratedPairColored source.1)))
  (hdegree : forall (profile : SixVertexHorizontalBoundedFineRowProfile T) (source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile) (target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile), SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile source target -> (Finset.univ.filter fun otherSource => SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile otherSource target).card <= (Finset.univ.filter (SixVertexLoopResolvedUnitCrossFineRelated middle hmiddle_pos hmiddle_lt profile source)).card) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedUnitCrossRelationEdgeDegree middle hmiddle_pos hmiddle_lt hne hdegree


-- created on 2026-10-23

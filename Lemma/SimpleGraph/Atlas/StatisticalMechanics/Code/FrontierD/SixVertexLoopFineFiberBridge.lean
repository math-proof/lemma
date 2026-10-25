import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopFineFiberBridge.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexConfigurationPairTotalC_eq_fineProfileGrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean)
-/
@[path]
private lemma sixVertexConfigurationPairTotalC_eq_fineProfileGrade_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {pair : SixVertexConfigurationPairFineProfileFiber T left right profile} :
-- imply
  sixVertexConfigurationPairTotalC pair.1 = (sixVertexHorizontalFineRowProfileGrade profile).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexConfigurationPairTotalC_eq_fineProfileGrade pair

/--
[card_sixVertexConfigurationPairFineProfileFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean)
-/
@[path]
private lemma card_sixVertexConfigurationPairFineProfileFiber_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T} :
-- imply
  Fintype.card (SixVertexConfigurationPairFineProfileFiber T left right profile) = sixVertexHorizontalFineRowProfileSectorPairSum T left right profile := by
-- proof
  apply StatMech.FrontierD.card_sixVertexConfigurationPairFineProfileFiber T left right profile

/--
[card_sixVertexLoopDecoratedPairFineProfileFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean)
-/
@[path]
private lemma card_sixVertexLoopDecoratedPairFineProfileFiber_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T} :
-- imply
  Fintype.card (SixVertexLoopDecoratedPairFineProfileFiber T left right profile) = sixVertexHorizontalFineRowProfileSectorPairSum T left right profile * 2 ^ (sixVertexHorizontalFineRowProfileGrade profile).1 := by
-- proof
  apply StatMech.FrontierD.card_sixVertexLoopDecoratedPairFineProfileFiber T left right profile

/--
[loopFineProfileFibers_of_relationEdgeDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean)
-/
@[path]
private lemma loopFineProfileFibers_of_relationEdgeDegree_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (related : forall profile : SixVertexHorizontalBoundedFineRowProfile T, SixVertexLoopDecoratedPairFineProfileFiber T sourceLeft sourceRight profile -> SixVertexLoopDecoratedPairFineProfileFiber T targetLeft targetRight profile -> Prop)
  (hne : forall profile source, (Finset.univ.filter (related profile source)).Nonempty)
  (hdegree : forall profile source target, related profile source target -> (Finset.univ.filter fun otherSource => related profile otherSource target).card <= (Finset.univ.filter (related profile source)).card) :
-- imply
  SixVertexLoopDecoratedPairFineProfileFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.loopFineProfileFibers_of_relationEdgeDegree related hne hdegree

/--
[rawFineProfile_of_loopFineProfileFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean)
-/
@[path]
private lemma rawFineProfile_of_loopFineProfileFibers_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (hfiber : SixVertexLoopDecoratedPairFineProfileFiberDominates T sourceLeft sourceRight targetLeft targetRight) :
-- imply
  forall profile : SixVertexHorizontalBoundedFineRowProfile T, 0 <= sixVertexHorizontalFineRowProfileSignedSum T sourceLeft sourceRight targetLeft targetRight profile := by
-- proof
  apply StatMech.FrontierD.rawFineProfile_of_loopFineProfileFibers hfiber

/--
[rawFineProfile_of_loopRelationEdgeDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean)
-/
@[path]
private lemma rawFineProfile_of_loopRelationEdgeDegree_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (related : forall profile : SixVertexHorizontalBoundedFineRowProfile T, SixVertexLoopDecoratedPairFineProfileFiber T sourceLeft sourceRight profile -> SixVertexLoopDecoratedPairFineProfileFiber T targetLeft targetRight profile -> Prop)
  (hne : forall profile source, (Finset.univ.filter (related profile source)).Nonempty)
  (hdegree : forall profile source target, related profile source target -> (Finset.univ.filter fun otherSource => related profile otherSource target).card <= (Finset.univ.filter (related profile source)).card) :
-- imply
  forall profile : SixVertexHorizontalBoundedFineRowProfile T, 0 <= sixVertexHorizontalFineRowProfileSignedSum T sourceLeft sourceRight targetLeft targetRight profile := by
-- proof
  apply StatMech.FrontierD.rawFineProfile_of_loopRelationEdgeDegree related hne hdegree

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopFineProfileFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopFineFiberBridge.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopFineProfileFibers_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hfiber : SixVertexLoopDecoratedPairFineProfileFiberDominates T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_loopFineProfileFibers T middle hmiddle_pos hmiddle_lt hfiber


-- created on 2026-10-23

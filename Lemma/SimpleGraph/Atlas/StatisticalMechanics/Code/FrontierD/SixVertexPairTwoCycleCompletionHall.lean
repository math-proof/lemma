import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexFineProfileCompletionPairArrows_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean)
-/
@[path]
private lemma sixVertexFineProfileCompletionPairArrows_equiv_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {pair : SixVertexConfigurationPairFineProfileFiber T left right profile} :
-- imply
  sixVertexHorizontalFineProfileCompletionPairArrows (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions T left right profile pair) = (pair.1.1.1, pair.1.2.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFineProfileCompletionPairArrows_equiv pair

/--
[SixVertexHorizontalFineProfileCompletionPairUnionEqual.twoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean)
-/
@[path]
private lemma twoCycle_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexHorizontalFineProfileCompletionPair T lower upper profile}
  {target : SixVertexHorizontalFineProfileCompletionPair T middle middle profile}
-- given
  (hunion : SixVertexHorizontalFineProfileCompletionPairUnionEqual source target) :
-- imply
  SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated source target := by
-- proof
  apply StatMech.FrontierD.SixVertexHorizontalFineProfileCompletionPairUnionEqual.twoCycle hunion

/--
[fineProfileCompletionPairTwoCycleRelated_equiv_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean)
-/
@[path]
private lemma fineProfileCompletionPairTwoCycleRelated_equiv_iff_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexConfigurationPairFineProfileFiber T lower upper profile}
  {target : SixVertexConfigurationPairFineProfileFiber T middle middle profile} :
-- imply
  SixVertexHorizontalFineProfileCompletionPairTwoCycleRelated (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions T lower upper profile source) (sixVertexConfigurationPairFineProfileFiberEquivHorizontalCompletions T middle middle profile target) <-> SixVertexConfigurationPairTwoCycleFineProfileRelated source target := by
-- proof
  apply StatMech.FrontierD.fineProfileCompletionPairTwoCycleRelated_equiv_iff source target

/--
[horizontalFineProfileCompletionTwoCycleMatching_of_unionMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean)
-/
@[path]
private lemma horizontalFineProfileCompletionTwoCycleMatching_of_unionMatching_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
-- given
  (hunion : SixVertexHorizontalFineProfileCompletionUnionMatching T lower middle upper) :
-- imply
  SixVertexHorizontalFineProfileCompletionTwoCycleMatching T lower middle upper := by
-- proof
  apply StatMech.FrontierD.horizontalFineProfileCompletionTwoCycleMatching_of_unionMatching hunion

/--
[horizontalFineProfileCompletionTwoCycleMatching_iff_fiberHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean)
-/
@[path]
private lemma horizontalFineProfileCompletionTwoCycleMatching_iff_fiberHall_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)} :
-- imply
  SixVertexHorizontalFineProfileCompletionTwoCycleMatching T lower middle upper <-> SixVertexConfigurationPairTwoCycleFineProfileFiberHall T lower middle upper := by
-- proof
  apply StatMech.FrontierD.horizontalFineProfileCompletionTwoCycleMatching_iff_fiberHall T lower middle upper

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_completionMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_completionMatching_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmatching : SixVertexHorizontalFineProfileCompletionTwoCycleMatching T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_completionMatching T middle hmiddle_pos hmiddle_lt hmatching

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_unionMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleCompletionHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_unionMatching_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmatching : SixVertexHorizontalFineProfileCompletionUnionMatching T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_unionMatching T middle hmiddle_pos hmiddle_lt hmatching


-- created on 2026-10-23

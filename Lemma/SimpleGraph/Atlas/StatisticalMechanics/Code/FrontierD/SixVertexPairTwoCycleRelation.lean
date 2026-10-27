import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleRelation
open StatMech StatMech.FrontierD


/--
[sixVertexPairAtMostTwoCycleRelated_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean)
-/
@[path]
private lemma sixVertexPairAtMostTwoCycleRelated_refl_eq
  {T : EvenTorus}
  {pair : SixVertexArrows T × SixVertexArrows T} :
-- imply
  sixVertexPairAtMostTwoCycleRelated pair pair := by
-- proof
  apply StatMech.FrontierD.sixVertexPairAtMostTwoCycleRelated_refl pair

/--
[sixVertexPairAtMostTwoCycleRelated_of_union_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean)
-/
@[path]
private lemma sixVertexPairAtMostTwoCycleRelated_of_union_eq_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hhorizontal : sixVertexPairUnionHorizontal source = sixVertexPairUnionHorizontal target)
  (hvertical : sixVertexPairUnionVertical source = sixVertexPairUnionVertical target) :
-- imply
  sixVertexPairAtMostTwoCycleRelated source target := by
-- proof
  apply StatMech.FrontierD.sixVertexPairAtMostTwoCycleRelated_of_union_eq hhorizontal hvertical

/--
[sixVertexPairAtMostTwoCycleFineRelated_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean)
-/
@[path]
private lemma sixVertexPairAtMostTwoCycleFineRelated_refl_eq
  {T : EvenTorus}
  {pair : SixVertexArrows T × SixVertexArrows T} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated pair pair := by
-- proof
  apply StatMech.FrontierD.sixVertexPairAtMostTwoCycleFineRelated_refl pair

/--
[sixVertexPairAtMostTwoCycleRelated_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean)
-/
@[path]
private lemma sixVertexPairAtMostTwoCycleRelated_symm_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hrelated : sixVertexPairAtMostTwoCycleRelated source target) :
-- imply
  sixVertexPairAtMostTwoCycleRelated target source := by
-- proof
  apply StatMech.FrontierD.sixVertexPairAtMostTwoCycleRelated_symm hrelated

/--
[sixVertexPairAtMostTwoCycleFineRelated_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean)
-/
@[path]
private lemma sixVertexPairAtMostTwoCycleFineRelated_symm_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated target source := by
-- proof
  apply StatMech.FrontierD.sixVertexPairAtMostTwoCycleFineRelated_symm hrelated

/--
[sixVertexPairAtMostTwoCycleFineRelated_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairTwoCycleRelation.lean)
-/
@[path]
private lemma sixVertexPairAtMostTwoCycleFineRelated_totalC_eq
  {T : EvenTorus}
  {source target : SixVertexArrows T × SixVertexArrows T}
-- given
  (hrelated : sixVertexPairAtMostTwoCycleFineRelated source target) :
-- imply
  sixVertexTorusCTypeCount source.1 + sixVertexTorusCTypeCount source.2 = sixVertexTorusCTypeCount target.1 + sixVertexTorusCTypeCount target.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexPairAtMostTwoCycleFineRelated_totalC hrelated


-- created on 2026-10-23

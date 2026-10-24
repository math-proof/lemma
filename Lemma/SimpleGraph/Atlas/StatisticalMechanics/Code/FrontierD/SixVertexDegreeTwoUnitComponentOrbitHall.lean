import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoUnitComponentOrbitHall
open Finset StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitPresentation StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitAtlas


/--
[SixVertexDegreeTwoUnitStrandPhysicalRelated.fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma fineRelated_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {target : SixVertexConfigurationPhysicalTarget T middle}
-- given
  (hrelated : SixVertexDegreeTwoUnitStrandPhysicalRelated source target) :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated (source.1.1, source.2.1) (target.1.1, target.2.1) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalRelated.fineRelated hrelated

/--
[SixVertexDegreeTwoUnitStrandPhysicalRelated.layers_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma layers_ne_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width}
  {source : SixVertexConfigurationPhysicalSource T middle hmiddle_pos hmiddle_lt}
  {target : SixVertexConfigurationPhysicalTarget T middle}
-- given
  (hrelated : SixVertexDegreeTwoUnitStrandPhysicalRelated source target) :
-- imply
  target.1 ≠ target.2 := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitStrandPhysicalRelated.layers_ne hrelated

/--
[sourceEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma sourceEquiv_val_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle hmiddle_pos hmiddle_lt Component k}
  {source : BooleanLayer Component (k + 1)} :
-- imply
  (orbit.sourceEquiv source).1 = orbit.sourceEmbedding source := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitPresentation.sourceEquiv_val orbit source

/--
[targetEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma targetEquiv_val_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle hmiddle_pos hmiddle_lt Component k}
  {target : BooleanLayer Component k} :
-- imply
  (orbit.targetEquiv target).1 = orbit.targetEmbedding target := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitPresentation.targetEquiv_val orbit target

/--
[related_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma related_equiv_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle hmiddle_pos hmiddle_lt Component k}
  {source : BooleanLayer Component (k + 1)}
  {target : BooleanLayer Component k} :
-- imply
  orbit.Related (orbit.sourceEquiv source) (orbit.targetEquiv target) <-> booleanMiddleLayerDownRelation source target := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitPresentation.related_equiv orbit source target

/--
[exists_booleanMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma exists_booleanMatching_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle hmiddle_pos hmiddle_lt Component k} :
-- imply
  ∃ matching : BooleanLayer Component (k + 1) → BooleanLayer Component k, Function.Injective matching ∧ ∀ source, booleanMiddleLayerDownRelation source (matching source) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitPresentation.exists_booleanMatching orbit

/--
[booleanMatching_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma booleanMatching_related_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle hmiddle_pos hmiddle_lt Component k}
  {source : BooleanLayer Component (k + 1)} :
-- imply
  SixVertexDegreeTwoUnitStrandPhysicalRelated (orbit.sourceEmbedding source) (orbit.targetEmbedding (orbit.booleanMatching source)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitPresentation.booleanMatching_related orbit source

/--
[hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma hall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {orbit : SixVertexDegreeTwoUnitComponentOrbitPresentation T middle hmiddle_pos hmiddle_lt Component k} :
-- imply
  orbit.Hall := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitPresentation.hall orbit

/--
[matching_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma matching_related_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle hmiddle_pos hmiddle_lt Source}
  {source : Source} :
-- imply
  atlas.Related source (atlas.matching source) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitAtlas.matching_related atlas source

/--
[hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoUnitComponentOrbitHall.lean)
-/
@[path]
private lemma hall_eq_2
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {atlas : SixVertexDegreeTwoUnitComponentOrbitAtlas T middle hmiddle_pos hmiddle_lt Source} :
-- imply
  forall sources : Finset Source, sources.card <= (Finset.univ.filter fun target : SixVertexConfigurationPhysicalTarget T middle => ∃ source ∈ sources, atlas.Related source target).card := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoUnitComponentOrbitAtlas.hall atlas


-- created on 2026-10-23

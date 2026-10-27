import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexUnitComponentHall
open Finset StatMech StatMech.FrontierD


/--
[booleanMiddleLayerAddedElement_mem_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUnitComponentHall.lean)
-/
@[path]
private lemma booleanMiddleLayerAddedElement_mem_source_eq
  [Fintype Component]
  {k : Nat}
  {target : BooleanLayer Component k}
  {source : BooleanLayer Component (k + 1)} :
-- imply
  booleanMiddleLayerAddedElement target source ∈ source.1 := by
-- proof
  apply StatMech.FrontierD.booleanMiddleLayerAddedElement_mem_source target source

/--
[booleanMiddleLayerAddedElement_not_mem_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUnitComponentHall.lean)
-/
@[path]
private lemma booleanMiddleLayerAddedElement_not_mem_target_eq
  [Fintype Component]
  {k : Nat}
  {target : BooleanLayer Component k}
  {source : BooleanLayer Component (k + 1)} :
-- imply
  booleanMiddleLayerAddedElement target source ∉ target.1 := by
-- proof
  apply StatMech.FrontierD.booleanMiddleLayerAddedElement_not_mem_target target source

/--
[booleanMiddleLayer_source_eq_insert_addedElement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUnitComponentHall.lean)
-/
@[path]
private lemma booleanMiddleLayer_source_eq_insert_addedElement_eq
  [Fintype Component]
  {k : Nat}
  {target : BooleanLayer Component k}
  {source : BooleanLayer Component (k + 1)}
-- given
  (hrelated : booleanMiddleLayerDownRelation source target) :
-- imply
  source.1 = insert (booleanMiddleLayerAddedElement target source) target.1 := by
-- proof
  apply StatMech.FrontierD.booleanMiddleLayer_source_eq_insert_addedElement target source hrelated

/--
[booleanMiddleLayerDownRelation_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUnitComponentHall.lean)
-/
@[path]
private lemma booleanMiddleLayerDownRelation_hall_eq
  [Fintype Component]
  {k : Nat}
-- given
  (hcard : Fintype.card Component = 2 * k) :
-- imply
  forall sources : Finset (BooleanLayer Component (k + 1)), sources.card <= (Finset.univ.filter fun target : BooleanLayer Component k => ∃ source ∈ sources, booleanMiddleLayerDownRelation source target).card := by
-- proof
  apply StatMech.FrontierD.booleanMiddleLayerDownRelation_hall k hcard


-- created on 2026-10-23

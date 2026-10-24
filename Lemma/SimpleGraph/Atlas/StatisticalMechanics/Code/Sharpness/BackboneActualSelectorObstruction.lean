import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorObstruction
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[shb_singleEdgeGraph_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean)
-/
@[path]
private lemma shb_singleEdgeGraph_edge_mem_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  s(x, y) ∈ (shb_singleEdgeGraph x y).edgeFinset := by
-- proof
  apply StatMech.Sharpness.shb_singleEdgeGraph_edge_mem hxy

/--
[shb_singleEdgeGraph_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean)
-/
@[path]
private lemma shb_singleEdgeGraph_edgeFinset_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  (shb_singleEdgeGraph x y).edgeFinset = {s(x, y)} := by
-- proof
  apply StatMech.Sharpness.shb_singleEdgeGraph_edgeFinset hxy

/--
[shb_singleEdgeFlux_incidentFlux_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean)
-/
@[path]
private lemma shb_singleEdgeFlux_incidentFlux_left_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  incidentFlux (shb_emptyActiveSingleEdgeDomain x y).graph (ofEdgeFun (shb_emptyActiveSingleEdgeDomain x y).graph (shb_singleEdgeFlux x y)) x = 1 := by
-- proof
  apply StatMech.Sharpness.shb_singleEdgeFlux_incidentFlux_left hxy

/--
[shb_singleEdgeFlux_sources_ne_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean)
-/
@[path]
private lemma shb_singleEdgeFlux_sources_ne_empty_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  sources (shb_emptyActiveSingleEdgeDomain x y).graph (ofEdgeFun (shb_emptyActiveSingleEdgeDomain x y).graph (shb_singleEdgeFlux x y)) ≠ ∅ := by
-- proof
  apply StatMech.Sharpness.shb_singleEdgeFlux_sources_ne_empty hxy

/--
[shb_CurrentDynamicSelector_isEmpty_of_exists_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean)
-/
@[path]
private lemma shb_CurrentDynamicSelector_isEmpty_of_exists_ne_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
-- given
  (hne : ∃ x : V, ∃ y : V, x ≠ y) :
-- imply
  IsEmpty (shb_CurrentDynamicSelector (V := V)) := by
-- proof
  apply StatMech.Sharpness.shb_CurrentDynamicSelector_isEmpty_of_exists_ne hne

/--
[shb_no_CurrentDynamicSelector_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean)
-/
@[path]
private lemma shb_no_CurrentDynamicSelector_bool_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V] :
-- imply
  IsEmpty (shb_CurrentDynamicSelector (V := Bool)) := by
-- proof
  apply StatMech.Sharpness.shb_no_CurrentDynamicSelector_bool

/--
[shb_singleEdge_rawSplit_zero_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean)
-/
@[path]
private lemma shb_singleEdge_rawSplit_zero_two_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  weight (shb_singleEdgeGraph x y) 1 (fun _ => 1) (ofEdgeFun (shb_singleEdgeGraph x y) (shb_singleEdgeConstantFlux x y 0)) * weight (shb_singleEdgeGraph x y) 1 (fun _ => 1) (ofEdgeFun (shb_singleEdgeGraph x y) (shb_singleEdgeConstantFlux x y 2)) = (1 / 2 : Real) := by
-- proof
  apply StatMech.Sharpness.shb_singleEdge_rawSplit_zero_two hxy

/--
[shb_singleEdge_rawSplit_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean)
-/
@[path]
private lemma shb_singleEdge_rawSplit_one_one_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  weight (shb_singleEdgeGraph x y) 1 (fun _ => 1) (ofEdgeFun (shb_singleEdgeGraph x y) (shb_singleEdgeConstantFlux x y 1)) * weight (shb_singleEdgeGraph x y) 1 (fun _ => 1) (ofEdgeFun (shb_singleEdgeGraph x y) (shb_singleEdgeConstantFlux x y 1)) = (1 : Real) := by
-- proof
  apply StatMech.Sharpness.shb_singleEdge_rawSplit_one_one hxy

/--
[shb_singleEdge_edgeCopyMultiplicity_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean)
-/
@[path]
private lemma shb_singleEdge_edgeCopyMultiplicity_two_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  2 * (weight (shb_singleEdgeGraph x y) 1 (fun _ => 1) (ofEdgeFun (shb_singleEdgeGraph x y) (shb_singleEdgeConstantFlux x y 0)) * weight (shb_singleEdgeGraph x y) 1 (fun _ => 1) (ofEdgeFun (shb_singleEdgeGraph x y) (shb_singleEdgeConstantFlux x y 2))) = weight (shb_singleEdgeGraph x y) 1 (fun _ => 1) (ofEdgeFun (shb_singleEdgeGraph x y) (shb_singleEdgeConstantFlux x y 1)) * weight (shb_singleEdgeGraph x y) 1 (fun _ => 1) (ofEdgeFun (shb_singleEdgeGraph x y) (shb_singleEdgeConstantFlux x y 1)) := by
-- proof
  apply StatMech.Sharpness.shb_singleEdge_edgeCopyMultiplicity_two hxy


-- created on 2026-10-23

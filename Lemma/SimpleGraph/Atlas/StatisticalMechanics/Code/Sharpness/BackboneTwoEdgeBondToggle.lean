import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle
open SimpleGraph Finset StatMech StatMech.Sharpness StatMech.Sharpness.BackboneTwoEdgeBondToggle


/--
[firstCopy_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma firstCopy_edge_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  (firstCopy G e f hne).1 = e := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.firstCopy_edge G e f hne

/--
[secondCopy_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma secondCopy_edge_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  (secondCopy G e f hne).1 = f := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.secondCopy_edge G e f hne

/--
[firstCopy_ne_secondCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma firstCopy_ne_secondCopy_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  firstCopy G e f hne ≠ secondCopy G e f hne := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.firstCopy_ne_secondCopy G e f hne

/--
[copy_eq_first_or_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma copy_eq_first_or_second_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
  {i : Copy G (twoUnitFlux G e f)}
-- given
  (hne : e ≠ f) :
-- imply
  i = firstCopy G e f hne ∨ i = secondCopy G e f hne := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.copy_eq_first_or_second G e f hne i

/--
[copy_univ_eq_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma copy_univ_eq_pair_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  (univ : Finset (Copy G (twoUnitFlux G e f))) = {firstCopy G e f hne, secondCopy G e f hne} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.copy_univ_eq_pair G e f hne

/--
[subset_eq_of_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma subset_eq_of_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
  {T : Finset (Copy G (twoUnitFlux G e f))}
-- given
  (hne : e ≠ f) :
-- imply
  T = ∅ ∨ T = {firstCopy G e f hne} ∨ T = {secondCopy G e f hne} ∨ T = {firstCopy G e f hne, secondCopy G e f hne} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.subset_eq_of_twoUnitFlux G e f hne T

/--
[activeSegmentFiber_unitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma activeSegmentFiber_unitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
-- imply
  shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hactive (unitFlux d.graph e) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.activeSegmentFiber_unitFlux d e hactive

/--
[scan_after_unitFlux_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma scan_after_unitFlux_none_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset} :
-- imply
  scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit (unitFlux d.graph e) b) ⟨d, [e.1]⟩ = none := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.scan_after_unitFlux_none d e

/--
[program_complete_canonical_singleton_unitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma program_complete_canonical_singleton_unitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (hactive : canonicalEdgeSegment d.graph e ∈ d.active) :
-- imply
  BackboneTwoEdgeBondProgram.program.CompleteEvent d [canonicalEdgeSegment d.graph e] (unitFlux d.graph e) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.program_complete_canonical_singleton_unitFlux d e hactive

/--
[secondEdge_mem_delete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma secondEdge_mem_delete_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  f.1 ∈ (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.secondEdge_mem_delete d e f hne

/--
[residualEdge_canonical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma residualEdge_canonical_eq_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  canonicalEdgeSegment (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet) (residualEdge d e f hne) = canonicalEdgeSegment d.graph f := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.residualEdge_canonical_eq d e f hne

/--
[distinct_canonical_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma distinct_canonical_compatible_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  shb_BackboneExplorationDomain.compatible (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.distinct_canonical_compatible d e f hne

/--
[residualEdge_active_advance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma residualEdge_active_advance_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hactive : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  canonicalEdgeSegment (shb_BackboneExplorationDomain.advance d (canonicalEdgeSegment d.graph e)).graph (residualEdge d e f hne) ∈ (shb_BackboneExplorationDomain.advance d (canonicalEdgeSegment d.graph e)).active := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.residualEdge_active_advance d e f hne hactive

/--
[extendFlux_residual_unitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma extendFlux_residual_unitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  extendFlux (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) (unitFlux (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet) (residualEdge d e f hne)) = unitFlux d.graph f := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.extendFlux_residual_unitFlux d e f hne

/--
[firstEndpoints_ne_secondEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma firstEndpoints_ne_secondEndpoints_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e) (canonicalEdgeSegment G f)) :
-- imply
  ({(canonicalEdgeSegment G e).1, (canonicalEdgeSegment G e).2.1} : Finset V) ≠ ({(canonicalEdgeSegment G f).1, (canonicalEdgeSegment G f).2.1} : Finset V) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.firstEndpoints_ne_secondEndpoints G e f hpath

/--
[firstEndpoints_ne_pairBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma firstEndpoints_ne_pairBoundary_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e) (canonicalEdgeSegment G f)) :
-- imply
  ({(canonicalEdgeSegment G e).1, (canonicalEdgeSegment G e).2.1} : Finset V) ≠ ({(canonicalEdgeSegment G e).1, (canonicalEdgeSegment G e).2.1} ∆ {(canonicalEdgeSegment G f).1, (canonicalEdgeSegment G f).2.1} : Finset V) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.firstEndpoints_ne_pairBoundary G e f hpath

/--
[secondEndpoints_ne_pairBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma secondEndpoints_ne_pairBoundary_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment G e) (canonicalEdgeSegment G f)) :
-- imply
  ({(canonicalEdgeSegment G f).1, (canonicalEdgeSegment G f).2.1} : Finset V) ≠ ({(canonicalEdgeSegment G e).1, (canonicalEdgeSegment G e).2.1} ∆ {(canonicalEdgeSegment G f).1, (canonicalEdgeSegment G f).2.1} : Finset V) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.secondEndpoints_ne_pairBoundary G e f hpath

/--
[sources_ofEdgeFun_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma sources_ofEdgeFun_zero_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V} :
-- imply
  sources G (ofEdgeFun G (0 : G.edgeFinset -> Nat)) = ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.sources_ofEdgeFun_zero G

/--
[program_pair_zero_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma program_pair_zero_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  ¬BackboneTwoEdgeBondProgram.program.CompleteEvent d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.program_pair_zero_false d e f hpath

/--
[program_pair_unitFlux_first_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma program_pair_unitFlux_first_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  ¬BackboneTwoEdgeBondProgram.program.CompleteEvent d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (unitFlux d.graph e) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.program_pair_unitFlux_first_false d e f hpath

/--
[program_pair_unitFlux_second_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma program_pair_unitFlux_second_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  ¬BackboneTwoEdgeBondProgram.program.CompleteEvent d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f] (unitFlux d.graph f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.program_pair_unitFlux_second_false d e f hpath

/--
[activeSegmentFiber_zero_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma activeSegmentFiber_zero_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (hs : canonicalEdgeSegment d.graph e ∈ d.active) :
-- imply
  ¬shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hs 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.activeSegmentFiber_zero_false d e hs

/--
[activeSegmentFiber_second_unitFlux_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma activeSegmentFiber_second_unitFlux_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hs : canonicalEdgeSegment d.graph e ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  ¬shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hs (unitFlux d.graph f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.activeSegmentFiber_second_unitFlux_false d e f hs hpath

/--
[activeSegmentFiber_twoUnitFlux_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma activeSegmentFiber_twoUnitFlux_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hs : canonicalEdgeSegment d.graph e ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  ¬shb_ActiveSegmentFiber d (canonicalEdgeSegment d.graph e) hs (twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.activeSegmentFiber_twoUnitFlux_false d e f hs hpath

/--
[profileFlux_singleton_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma profileFlux_singleton_apply_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {i : Copy G m}
  {g : G.edgeFinset}
-- given
  (m : G.edgeFinset -> Nat) :
-- imply
  profileFlux G m {i} g = if i.1 = g then 1 else 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.profileFlux_singleton_apply G m i g

/--
[profileFlux_pair_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma profileFlux_pair_apply_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {i j : Copy G m}
  {g : G.edgeFinset}
-- given
  (m : G.edgeFinset -> Nat)
  (hij : i ≠ j) :
-- imply
  profileFlux G m {i, j} g = (if i.1 = g then 1 else 0) + (if j.1 = g then 1 else 0) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.profileFlux_pair_apply G m i j hij g

/--
[profileFlux_empty_twoUnitFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma profileFlux_empty_twoUnitFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  profileFlux G (twoUnitFlux G e f) (∅ : Finset (Copy G (twoUnitFlux G e f))) = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.profileFlux_empty_twoUnitFlux G e f hne

/--
[profileFlux_firstCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma profileFlux_firstCopy_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  profileFlux G (twoUnitFlux G e f) {firstCopy G e f hne} = unitFlux G e := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.profileFlux_firstCopy G e f hne

/--
[profileFlux_secondCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma profileFlux_secondCopy_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  profileFlux G (twoUnitFlux G e f) {secondCopy G e f hne} = unitFlux G f := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.profileFlux_secondCopy G e f hne

/--
[profileFlux_bothCopies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma profileFlux_bothCopies_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  profileFlux G (twoUnitFlux G e f) {firstCopy G e f hne, secondCopy G e f hne} = twoUnitFlux G e f := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.profileFlux_bothCopies G e f hne

/--
[empty_symmDiff_secondCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma empty_symmDiff_secondCopy_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  (∅ : Finset (Copy G (twoUnitFlux G e f))) ∆ ({secondCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f))) = ({secondCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f))) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.empty_symmDiff_secondCopy G e f hne

/--
[firstCopy_symmDiff_secondCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma firstCopy_symmDiff_secondCopy_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  ({firstCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f))) ∆ {secondCopy G e f hne} = ({firstCopy G e f hne, secondCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f))) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.firstCopy_symmDiff_secondCopy G e f hne

/--
[secondCopy_symmDiff_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma secondCopy_symmDiff_self_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  ({secondCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f))) ∆ {secondCopy G e f hne} = (∅ : Finset (Copy G (twoUnitFlux G e f))) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.secondCopy_symmDiff_self G e f hne

/--
[bothCopies_symmDiff_secondCopy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma bothCopies_symmDiff_secondCopy_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  ({firstCopy G e f hne, secondCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f))) ∆ {secondCopy G e f hne} = ({firstCopy G e f hne} : Finset (Copy G (twoUnitFlux G e f))) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.bothCopies_symmDiff_secondCopy G e f hne

/--
[bondwiseRunToggleCovariance_twoUnit_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma bondwiseRunToggleCovariance_twoUnit_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {E F : BondwiseRunSpec V}
  {G : SimpleGraph V}
  {e f : G.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  BondwiseRunToggleCovariance E F G (twoUnitFlux G e f) {secondCopy G e f hne} <-> (E.Event G 0 <-> F.Event G (unitFlux G f)) /\ (E.Event G (unitFlux G e) <-> F.Event G (twoUnitFlux G e f)) /\ (E.Event G (unitFlux G f) <-> F.Event G 0) /\ (E.Event G (twoUnitFlux G e f) <-> F.Event G (unitFlux G e)) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.bondwiseRunToggleCovariance_twoUnit_iff E F G e f hne

/--
[fullRun_activeHead_twoUnit_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma fullRun_activeHead_twoUnit_covariance_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph BackboneConcreteBondProgram.oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  BondwiseRunToggleCovariance ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.fullRun_activeHead_twoUnit_covariance d e f hne hfirst hactiveE hactiveF hpath

/--
[firstEdge_not_mem_delete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma firstEdge_not_mem_delete_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset} :
-- imply
  e.1 ∉ (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.firstEdge_not_mem_delete d e

/--
[extendFlux_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma extendFlux_zero_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset} :
-- imply
  extendFlux (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) (0 : (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) = 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.extendFlux_zero d e

/--
[liftedPredicate_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma liftedPredicate_zero_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (P : ((d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) -> Prop) :
-- imply
  LiftedPredicate (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) P 0 <-> P 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.liftedPredicate_zero_iff d e P

/--
[liftedPredicate_second_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma liftedPredicate_second_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (P : ((d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) -> Prop) :
-- imply
  LiftedPredicate (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) P (unitFlux d.graph f) <-> P (unitFlux (d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet) (residualEdge d e f hne)) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.liftedPredicate_second_iff d e f hne P

/--
[not_lifted_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma not_lifted_first_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset}
-- given
  (P : ((d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) -> Prop) :
-- imply
  ¬LiftedPredicate (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) P (unitFlux d.graph e) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.not_lifted_first d e P

/--
[not_lifted_twoUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma not_lifted_twoUnit_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (P : ((d.graph.deleteEdges (canonicalEdgeSegment d.graph e).edgeSet).edgeFinset -> Nat) -> Prop) :
-- imply
  ¬LiftedPredicate (d.graph.deleteEdges_le (canonicalEdgeSegment d.graph e).edgeSet) P (twoUnitFlux d.graph e f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.not_lifted_twoUnit d e f hne P

/--
[vacuum_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma vacuum_zero_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e : d.graph.edgeFinset} :
-- imply
  (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)).Event d.graph 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.vacuum_zero d e

/--
[vacuum_second_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma vacuum_second_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f) :
-- imply
  ¬(residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)).Event d.graph (unitFlux d.graph f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.vacuum_second_false d e f hne

/--
[suffix_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma suffix_second_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]).Event d.graph (unitFlux d.graph f) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.suffix_second d e f hne hactiveF

/--
[suffix_zero_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma suffix_zero_false_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset} :
-- imply
  ¬((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]).Event d.graph 0 := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.suffix_zero_false d e f

/--
[residualVacuum_suffix_twoUnit_truthTable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma residualVacuum_suffix_twoUnit_truthTable_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  let vacuum := residualVacuumRunSpec d (canonicalEdgeSegment d.graph e) let suffix := (BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f] (vacuum.Event d.graph 0 /\ suffix.Event d.graph (unitFlux d.graph f)) /\ (¬vacuum.Event d.graph (unitFlux d.graph e) /\ ¬suffix.Event d.graph (twoUnitFlux d.graph e f)) /\ (¬vacuum.Event d.graph (unitFlux d.graph f) /\ ¬suffix.Event d.graph 0) /\ (¬vacuum.Event d.graph (twoUnitFlux d.graph e f) /\ ¬suffix.Event d.graph (unitFlux d.graph e)) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.residualVacuum_suffix_twoUnit_truthTable d e f hne hactiveF

/--
[residualVacuum_suffix_twoUnit_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma residualVacuum_suffix_twoUnit_covariance_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active) :
-- imply
  BondwiseRunToggleCovariance (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.residualVacuum_suffix_twoUnit_covariance d e f hne hactiveF

/--
[twoUnit_componentwise_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma twoUnit_componentwise_covariance_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  BondwiseRunToggleCovariance ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} /\ BondwiseRunToggleCovariance (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.twoUnit_componentwise_covariance d e f hne hfirst hactiveE hactiveF hpath

/--
[twoUnit_pair_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma twoUnit_pair_toggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
  {T : Finset (Copy d.graph (twoUnitFlux d.graph e f))}
-- given
  (hne : e ≠ f)
  (hfirst : scan.firstAdmissible (fun _ b => fluxBitConfig d.graph oddBit (twoUnitFlux d.graph e f) b) ⟨d, []⟩ = some e.1)
  (hactiveE : canonicalEdgeSegment d.graph e ∈ d.active)
  (hactiveF : canonicalEdgeSegment d.graph f ∈ d.active)
  (hpath : FormsTwoEdgePath (canonicalEdgeSegment d.graph e) (canonicalEdgeSegment d.graph f)) :
-- imply
  BondwisePairEvent ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) d.graph (twoUnitFlux d.graph e f) T <-> BondwisePairEvent (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hactiveE) ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph (twoUnitFlux d.graph e f) (T ∆ {secondCopy d.graph e f hne}) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.twoUnit_pair_toggle d e f hne hfirst hactiveE hactiveF hpath T

/--
[twoUnit_componentwise_covariance_iff_eventTable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma twoUnit_componentwise_covariance_iff_eventTable_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
-- given
  (hne : e ≠ f)
  (hs : canonicalEdgeSegment d.graph e ∈ d.active) :
-- imply
  (BondwiseRunToggleCovariance ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hs) d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne} /\ BondwiseRunToggleCovariance (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph (twoUnitFlux d.graph e f) {secondCopy d.graph e f hne}) <-> TwoUnitComponentwiseEventTable d e f hne hs := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.twoUnit_componentwise_covariance_iff_eventTable d e f hne hs

/--
[twoUnit_pair_toggle_of_eventTable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeBondToggle.lean)
-/
@[path]
private lemma twoUnit_pair_toggle_of_eventTable_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_ExplorationDomain V}
  {e f : d.graph.edgeFinset}
  {T : Finset (Copy d.graph (twoUnitFlux d.graph e f))}
-- given
  (hne : e ≠ f)
  (hs : canonicalEdgeSegment d.graph e ∈ d.active)
  (htable : TwoUnitComponentwiseEventTable d e f hne hs) :
-- imply
  BondwisePairEvent ((BackboneTwoEdgeBondProgram.program (V := V)).runSpec d [canonicalEdgeSegment d.graph e, canonicalEdgeSegment d.graph f]) (residualVacuumRunSpec d (canonicalEdgeSegment d.graph e)) d.graph (twoUnitFlux d.graph e f) T <-> BondwisePairEvent (activeSegmentRunSpec d (canonicalEdgeSegment d.graph e) hs) ((BackboneTwoEdgeBondProgram.program (V := V)).liftedResidualRunSpec d (canonicalEdgeSegment d.graph e) [canonicalEdgeSegment d.graph f]) d.graph (twoUnitFlux d.graph e f) (T ∆ {secondCopy d.graph e f hne}) := by
-- proof
  apply StatMech.Sharpness.BackboneTwoEdgeBondToggle.twoUnit_pair_toggle_of_eventTable d e f hne hs htable T


-- created on 2026-10-23

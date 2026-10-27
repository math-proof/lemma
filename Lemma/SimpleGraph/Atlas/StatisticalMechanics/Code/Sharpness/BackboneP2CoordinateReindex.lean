import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateReindex.Part3
open SimpleGraph Finset BigOperators StatMech StatMech.Sharpness StatMech.Sharpness.BackboneP2CoordinateReindex


/--
[edgeFinset_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma edgeFinset_subset_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
-- given
  (hHG : H ≤ G) :
-- imply
  H.edgeFinset ⊆ G.edgeFinset := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.edgeFinset_subset hHG

/--
[extendFlux_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma extendFlux_injective_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
-- given
  (hHG : H ≤ G) :
-- imply
  Function.Injective (extendFlux hHG) := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.extendFlux_injective hHG

/--
[ofEdgeFun_extendFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma ofEdgeFun_extendFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
-- given
  (hHG : H ≤ G)
  (r : H.edgeFinset -> Nat) :
-- imply
  ofEdgeFun G (extendFlux hHG r) = ofEdgeFun H r := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.ofEdgeFun_extendFlux hHG r

/--
[incidentFlux_extendFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma incidentFlux_extendFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {x : V}
-- given
  (hHG : H ≤ G)
  (r : H.edgeFinset -> Nat) :
-- imply
  incidentFlux G (ofEdgeFun G (extendFlux hHG r)) x = incidentFlux H (ofEdgeFun H r) x := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.incidentFlux_extendFlux hHG r x

/--
[sources_extendFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma sources_extendFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
-- given
  (hHG : H ≤ G)
  (r : H.edgeFinset -> Nat) :
-- imply
  sources G (ofEdgeFun G (extendFlux hHG r)) = sources H (ofEdgeFun H r) := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.sources_extendFlux hHG r

/--
[weight_extendFlux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma weight_extendFlux_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {beta : Real}
-- given
  (hHG : H ≤ G)
  (J : Sym2 V -> Real)
  (r : H.edgeFinset -> Nat) :
-- imply
  weight G beta J (ofEdgeFun G (extendFlux hHG r)) = weight H beta J (ofEdgeFun H r) := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.weight_extendFlux hHG beta J r

/--
[liftedPredicate_witness_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma liftedPredicate_witness_unique_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {q : G.edgeFinset -> Nat}
  {r t : H.edgeFinset -> Nat}
-- given
  (hHG : H ≤ G)
  (hr : extendFlux hHG r = q)
  (ht : extendFlux hHG t = q) :
-- imply
  r = t := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.liftedPredicate_witness_unique hHG hr ht

/--
[tsum_liftedPredicate_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma tsum_liftedPredicate_eq_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {beta : Real}
  [DecidablePred P]
-- given
  (hHG : H ≤ G)
  (J : Sym2 V -> Real)
  (P : (H.edgeFinset -> Nat) -> Prop) :
-- imply
  (∑' q : G.edgeFinset -> Nat, if LiftedPredicate hHG P q then weight G beta J (ofEdgeFun G q) else 0) = ∑' r : H.edgeFinset -> Nat, if P r then weight H beta J (ofEdgeFun H r) else 0 := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.tsum_liftedPredicate_eq hHG beta J P

/--
[tsum_liftedVacuum_eq_currentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma tsum_liftedVacuum_eq_currentSum_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {beta : Real}
-- given
  (hHG : H ≤ G)
  (J : Sym2 V -> Real) :
-- imply
  (∑' q : G.edgeFinset -> Nat, if LiftedPredicate hHG (fun r => sources H (ofEdgeFun H r) = ∅) q then weight G beta J (ofEdgeFun G q) else 0) = currentSum H beta J ∅ := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.tsum_liftedVacuum_eq_currentSum hHG beta J

/--
[rawPairFiberMass_eq_rawSourcePairFiberMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma rawPairFiberMass_eq_rawSourcePairFiberMass_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
  [DecidablePred R]
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (m : d.graph.edgeFinset -> Nat)
  (R : (d.graph.edgeFinset -> Nat) -> Prop) :
-- imply
  rawPairFiberMass d.graph beta J m (S.Fiber d word) R = rawSourcePairFiberMass d.graph beta J m (S.sourceClass d word) (S.Fiber d word) R := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.rawPairFiberMass_eq_rawSourcePairFiberMass S beta J d word m R

/--
[partialActualMass_mul_residualCurrentSum_eq_pairTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma partialActualMass_mul_residualCurrentSum_eq_pairTsum_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real) :
-- imply
  S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m (S.sourceClass d (s :: ss)) (S.Fiber d (s :: ss)) (LiftedPredicate (d.graph.deleteEdges_le s.edgeSet) (fun r => sources (shb_BackboneExplorationDomain.advance d s).graph (ofEdgeFun (shb_BackboneExplorationDomain.advance d s).graph r) = ∅)) := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.partialActualMass_mul_residualCurrentSum_eq_pairTsum S beta J d s ss

/--
[segmentNum_eq_fiberTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma segmentNum_eq_fiberTsum_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active) :
-- imply
  shb_segmentNum beta J d s = ∑' p : d.graph.edgeFinset -> Nat, if shb_ActiveSegmentFiber d s hs p then weight d.graph beta J (ofEdgeFun d.graph p) else 0 := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.segmentNum_eq_fiberTsum beta J d s hs

/--
[rawPairFiberMass_eq_rawActivePairFiberMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma rawPairFiberMass_eq_rawActivePairFiberMass_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  [DecidablePred R]
-- given
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (m : d.graph.edgeFinset -> Nat)
  (R : (d.graph.edgeFinset -> Nat) -> Prop) :
-- imply
  rawPairFiberMass d.graph beta J m (shb_ActiveSegmentFiber d s hs) R = rawSourcePairFiberMass d.graph beta J m {s.1, s.2.1} (shb_ActiveSegmentFiber d s hs) R := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.rawPairFiberMass_eq_rawActivePairFiberMass beta J d s hs m R

/--
[segmentNum_mul_partialActualMass_eq_pairTsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma segmentNum_mul_partialActualMass_eq_pairTsum_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active) :
-- imply
  shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss = ∑' m : d.graph.edgeFinset -> Nat, rawSourcePairFiberMass d.graph beta J m {s.1, s.2.1} (shb_ActiveSegmentFiber d s hs) (LiftedPredicate (d.graph.deleteEdges_le s.edgeSet) (S.Fiber (shb_BackboneExplorationDomain.advance d s) ss)) := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.segmentNum_mul_partialActualMass_eq_pairTsum S beta J d s ss hs

/--
[actualMass_active_of_coordinateToggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean)
-/
@[path]
private lemma actualMass_active_of_coordinateToggle_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {beta : Real}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
  {path : ContributingPathSelector d.graph beta J (S.sourceClass d (s :: ss)) (stepToggleSource S d s ss) (S.Fiber d (s :: ss)) (liftedResidualVacuum d s) (shb_ActiveSegmentFiber d s hs) (liftedResidualFiber S d s ss)}
-- given
  (S : shb_PartialCurrentDynamicSelector (V := V))
  (J : Sym2 V -> Real)
  (hs : s ∈ d.active)
  (path_sources : ∀ m hm, RandomCurrent.sources (FluxEdgeCopy.endsM d.graph m) (path m hm) = stepToggleSource S d s ss)
  (transport : ∀ m hm T, (S.Fiber d (s :: ss) (FluxEdgeCopy.profileFlux d.graph m T) ∧ liftedResidualVacuum d s (FluxEdgeCopy.profileFlux d.graph m (univ \ T))) <-> (shb_ActiveSegmentFiber d s hs (FluxEdgeCopy.profileFlux d.graph m (T ∆ path m hm)) ∧ liftedResidualFiber S d s ss (FluxEdgeCopy.profileFlux d.graph m (univ \ (T ∆ path m hm))))) :
-- imply
  S.actualMass beta J d (s :: ss) * currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅ = shb_segmentNum beta J d s * S.actualMass beta J (shb_BackboneExplorationDomain.advance d s) ss := by
-- proof
  apply StatMech.Sharpness.BackboneP2CoordinateReindex.actualMass_active_of_coordinateToggle S beta J d s ss hs path path_sources transport


-- created on 2026-10-23

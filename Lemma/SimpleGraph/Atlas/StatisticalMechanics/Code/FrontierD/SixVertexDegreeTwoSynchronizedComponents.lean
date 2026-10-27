import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedComponents.Part31
open StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets


/--
[sixVertexDegreeTwoSynchronizedGraph_predecessors_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedGraph_predecessors_reachable_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d) (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedGraph_predecessors_reachable homega heta hdegree d

/--
[sixVertexDegreeTwoSynchronizedEdgeTransition_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedEdgeTransition_endpoints_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {edge : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Dart}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (edge.1.1 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge) /\ edge.1.2 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge)) \/ (edge.1.2 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge) /\ edge.1.1 = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true (sixVertexDegreeTwoSynchronizedEdgeTransition homega heta hdegree edge)) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedEdgeTransition_endpoints homega heta hdegree edge

/--
[sixVertexDegreeTwoSynchronizedComponentCharge_le_positiveDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponentCharge_le_positiveDarts_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component ≤ (sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree component).card := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponentCharge_le_positiveDarts homega heta hdegree component

/--
[exists_two_sixVertexDegreeTwoSynchronizedComponentPositiveDarts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma exists_two_sixVertexDegreeTwoSynchronizedComponentPositiveDarts_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hcharge : 2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component) :
-- imply
  ∃ first second : SixVertexOrientedDisagreementDart omega eta, first ≠ second /\ first ∈ sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree component /\ second ∈ sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree component := by
-- proof
  apply StatMech.FrontierD.exists_two_sixVertexDegreeTwoSynchronizedComponentPositiveDarts homega heta hdegree component hcharge

/--
[sixVertexDegreeTwoSynchronizedHighChargeSeed_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedHighChargeSeed_nonempty_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hcharge : 2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component) :
-- imply
  Nonempty (SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedHighChargeSeed_nonempty homega heta hdegree component hcharge

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.walk_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma walk_isPath_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.walk.IsPath := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.walk_isPath seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.walk_support_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma walk_support_nodup_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.walk.support.Nodup := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.walk_support_nodup seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.walk_length_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma walk_length_pos_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  0 < seed.walk.length := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.walk_length_pos seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transitions_length_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.transitions.length = seed.walk.length := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_length seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transitions_ne_nil_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.transitions ≠ [] := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_ne_nil seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transitionAt_endpoints_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {i : Fin seed.walk.length} :
-- imply
  (seed.walk.getVert i = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false (seed.transitionAt i) /\ seed.walk.getVert (i + 1) = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true (seed.transitionAt i)) \/ (seed.walk.getVert (i + 1) = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false (seed.transitionAt i) /\ seed.walk.getVert i = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true (seed.transitionAt i)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_endpoints seed i

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_getVert_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transitionAt_getVert_endpoints_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {i : Fin seed.walk.length} :
-- imply
  (seed.walk.getVert i = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false (seed.transitionAt i) /\ seed.walk.getVert (i + 1) = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true (seed.transitionAt i)) \/ (seed.walk.getVert (i + 1) = sixVertexDegreeTwoBranchPredecessor homega heta hdegree false (seed.transitionAt i) /\ seed.walk.getVert i = sixVertexDegreeTwoBranchPredecessor homega heta hdegree true (seed.transitionAt i)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_getVert_endpoints seed i

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transitionAt_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  Function.Injective seed.transitionAt := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_injective seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_eq_get](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transitionAt_eq_get_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {i : Fin seed.walk.length} :
-- imply
  seed.transitionAt i = seed.transitions.get (Fin.cast seed.transitions_length.symm i) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionAt_eq_get seed i

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transitions_nodup_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.transitions.Nodup := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transitions_nodup seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.mem_splitStates_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma mem_splitStates_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {x : DoubledAlignedState omega eta} :
-- imply
  x ∈ seed.splitStates ↔ x.1 ∈ seed.transitions := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.mem_splitStates_iff seed x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.branchSwap_mem_splitStates_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma branchSwap_mem_splitStates_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {x : DoubledAlignedState omega eta} :
-- imply
  doubledAlignedBranchSwap x ∈ seed.splitStates ↔ x ∈ seed.splitStates := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.branchSwap_mem_splitStates_iff seed x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma splitStates_length_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.splitStates.length = seed.transitions.length * 2 := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_length seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma splitStates_ne_nil_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.splitStates ≠ [] := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_ne_nil seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma splitStates_nodup_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.splitStates.Nodup := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.splitStates_nodup seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma splitBoundary_nodup_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  (doubledAlignedBoundarySegments homega heta hdegree false seed.splitStates).Nodup := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_nodup seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.first_seamSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma first_seamSign_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  sixVertexDegreeTwoStrandStepSeamSign hdegree seed.first = 1 := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.first_seamSign seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.second_seamSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma second_seamSign_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  sixVertexDegreeTwoStrandStepSeamSign hdegree seed.second = 1 := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.second_seamSign seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma splitBoundary_nonempty_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  Nonempty (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_nonempty seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_card_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma splitBoundary_card_pos_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  0 < Fintype.card (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.splitBoundary_card_pos seed

/--
[sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool} :
-- imply
  Function.Injective (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed layer) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed layer

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.occurrenceEquiv_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma occurrenceEquiv_self_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {slot : FKLayeredStrandSlot T} :
-- imply
  seed.occurrenceEquiv (seed.occurrenceEquiv slot) = slot := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.occurrenceEquiv_self seed slot

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.occurrenceEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma occurrenceEquiv_symm_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.occurrenceEquiv.symm = seed.occurrenceEquiv := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.occurrenceEquiv_symm seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.desiredTargetBoundary_intertwining](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma desiredTargetBoundary_intertwining_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {slot : FKLayeredStrandSlot T} :
-- imply
  seed.occurrenceEquiv (seed.desiredTargetBoundary slot) = fkColoredLayeredStrandSlotBoundaryPerm (fun layer => ((sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) layer).pairing) (seed.occurrenceEquiv slot) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.desiredTargetBoundary_intertwining seed slot

/--
[SixVertexDegreeTwoSynchronizedExactBoundaryTarget.slotIntertwining](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma slotIntertwining_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {target : SixVertexDegreeTwoSynchronizedExactBoundaryTarget seed} :
-- imply
  FKColoredIndexedOccurrenceSlotIntertwining (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) target.pairing (Fintype.card (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedExactBoundaryTarget.slotIntertwining target

/--
[SixVertexDegreeTwoSynchronizedExactBoundaryTarget.slotColorInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma slotColorInvariant_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {target : SixVertexDegreeTwoSynchronizedExactBoundaryTarget seed} :
-- imply
  FKColoredIndexedOccurrenceSlotColorInvariant (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) target.pairing (Fintype.card (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedExactBoundaryTarget.slotColorInvariant target

/--
[SixVertexDegreeTwoSynchronizedSupportedSplitTarget.preservesTotalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma preservesTotalC_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {supported : SixVertexDegreeTwoSynchronizedSupportedSplitTarget seed} :
-- imply
  supported.target.toSplice.PreservesTotalC := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedSupportedSplitTarget.preservesTotalC supported

/--
[key_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma key_splice_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed}
  {choice : Bool} :
-- imply
  (paired.key choice).splice = (paired.branch choice).target.toSplice := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets.key_splice paired choice

/--
[key_recovers_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma key_recovers_source_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed}
  {choice : Bool} :
-- imply
  (paired.key choice).splice.symm.target = sixVertexDegreeTwoAlignedColoredSource homega heta hdegree := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets.key_recovers_source paired choice

/--
[key_target_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma key_target_distinct_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {paired : SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets seed} :
-- imply
  (paired.key false).splice.target ≠ (paired.key true).splice.target := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedSupportedPairedSplitTargets.key_target_distinct paired

/--
[SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget.preservesTotalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma preservesTotalC_eq_2
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {supported : SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget seed} :
-- imply
  supported.target.colorSplice.PreservesTotalC := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedSupportedExactBoundaryTarget.preservesTotalC supported

/--
[sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_exists_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_exists_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {dart : FKMedialBlackDart T} :
-- imply
  (∃ i, sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed layer i = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) ↔ dart ∈ doubledAlignedBoundarySegments homega heta hdegree false seed.splitStates := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_exists_iff seed layer dart

/--
[sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false seed.splitStates) :
-- imply
  fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree (!layer) dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply seed layer dart hdart

/--
[sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply_of_not_mem_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (hdart : dart ∉ doubledAlignedBoundarySegments homega heta hdegree false seed.splitStates) :
-- imply
  fkIndexedOccurrenceSlotEquiv (Fintype.card (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedSplitOccurrenceSlotEquiv_apply_of_not_mem seed layer dart hdart

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.boundary_branchSwap_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma boundary_branchSwap_mem_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {x : DoubledAlignedState omega eta} :
-- imply
  doubledAlignedBlackDart homega heta hdegree false (doubledAlignedBranchSwap x) ∈ doubledAlignedBoundarySegments homega heta hdegree false seed.splitStates ↔ doubledAlignedBlackDart homega heta hdegree false x ∈ doubledAlignedBoundarySegments homega heta hdegree false seed.splitStates := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.boundary_branchSwap_mem_iff seed x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_branchSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selected_branchSwap_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.selected (doubledAlignedBranchSwap x) = seed.selected x := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_branchSwap seed x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_eq_selectedDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selected_eq_selectedDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.selected x = seed.selectedDart x.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_eq_selectedDart seed x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma synchronizedAt_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {d : SixVertexOrientedDisagreementDart omega eta} :
-- imply
  seed.synchronizedAt d ↔ seed.selectedDart (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d) = seed.selectedDart (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.synchronizedAt_iff seed d

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.unsynchronized_no_vertex_mask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma unsynchronized_no_vertex_mask_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {d : SixVertexOrientedDisagreementDart omega eta}
  {mask : Bool}
-- given
  (hunsync : ¬ seed.synchronizedAt d) :
-- imply
  (mask != seed.transitionBit (d, false)) = true ∨ (mask != seed.transitionBit (d, true)) = true := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.unsynchronized_no_vertex_mask seed d hunsync mask

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.globalSynchronization_or_noGo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma globalSynchronization_or_noGo_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.GloballySynchronized ∨ ∃ d, ∀ mask, (mask != seed.transitionBit (d, false)) = true ∨ (mask != seed.transitionBit (d, true)) = true := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.globalSynchronization_or_noGo seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selectedDart_eq_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selectedDart_eq_of_adj_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {first second : SixVertexOrientedDisagreementDart omega eta}
-- given
  (hsync : seed.GloballySynchronized)
  (hadj : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Adj first second) :
-- imply
  seed.selectedDart first = seed.selectedDart second := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selectedDart_eq_of_adj seed hsync hadj

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selectedDart_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selectedDart_eq_of_reachable_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {first second : SixVertexOrientedDisagreementDart omega eta}
-- given
  (hsync : seed.GloballySynchronized)
  (hreachable : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).Reachable first second) :
-- imply
  seed.selectedDart first = seed.selectedDart second := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selectedDart_eq_of_reachable seed hsync hreachable

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.globalSynchronization_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma globalSynchronization_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component} :
-- imply
  seed.GloballySynchronized ↔ ∀ first second : SixVertexOrientedDisagreementDart omega eta, (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk first = (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk second → seed.selectedDart first = seed.selectedDart second := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.globalSynchronization_iff seed

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transitionVertex_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.transitionVertex (doubledAlignedVertex x) = (seed.transitionBit (x.1, false) || seed.transitionBit (x.1, true)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex_active seed x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex_eq_bit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transitionVertex_eq_bit_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (hsync : seed.synchronizedAt d) :
-- imply
  seed.transitionVertex d.1.1.1 = seed.transitionBit (d, false) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transitionVertex_eq_bit seed d hsync

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma internalMismatchVertex_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.internalMismatchVertex (doubledAlignedVertex x) = (seed.selected x && ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP != (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.internalMismatchVertex_active seed x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma retieMask_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.retieMask layer (doubledAlignedVertex x) = ((seed.transitionBit (x.1, false) || seed.transitionBit (x.1, true)) || (seed.selected x && ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP != (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ))) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_active seed layer x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_eq_true_of_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma retieMask_eq_true_of_transition_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (htransition : seed.transitionBit x = true) :
-- imply
  seed.retieMask layer (doubledAlignedVertex x) = true := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_eq_true_of_transition seed layer x htransition

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_eq_true_of_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma retieMask_eq_true_of_internal_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
-- given
  (hselected : seed.selected x = true)
  (hpairing : ((orientedDartAlignedRetie homega heta hdegree x.1).pairingP != (orientedDartAlignedRetie homega heta hdegree x.1).pairingQ) = true) :
-- imply
  seed.retieMask layer (doubledAlignedVertex x) = true := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_eq_true_of_internal seed layer x hselected hpairing

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma targetPairing_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (hactive : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 2) :
-- imply
  let d := orientedDisagreementDartAtActiveVertex homega heta v hactive let transition := seed.transitionVertex v let internal := seed.internalMismatchVertex v seed.targetPairing layer v = if transition := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_active seed layer v hactive

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.sourceReturnState_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sourceReturnState_color_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta} :
-- imply
  sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer (seed.sourceReturnState layer x) = sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.sourceReturnState_color seed layer x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_inputState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selected_inputState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.selected (seed.inputState layer x) = seed.selected x := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_inputState seed layer x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_outputState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selected_outputState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.selected (seed.outputState layer x) = seed.selected x := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_outputState seed layer x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_tauAdjusted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selected_tauAdjusted_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.selected (sixVertexDegreeTwoTauAdjustedState homega heta hdegree x) = seed.selected x := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_tauAdjusted seed x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_sourceReturnState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selected_sourceReturnState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.selected (seed.sourceReturnState layer x) = seed.selected (doubledAlignedFirstReturnPerm homega heta hdegree x) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_sourceReturnState seed layer x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_activeReturnState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selected_activeReturnState_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.selected (seed.activeReturnState layer x) = seed.selected (doubledAlignedFirstReturnPerm homega heta hdegree (seed.inputState layer x)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_activeReturnState seed layer x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_activeReturnState_bne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma selected_activeReturnState_bne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta} :
-- imply
  (seed.selected (seed.activeReturnState layer x) != seed.selected x) = seed.transitionBit (doubledAlignedFirstReturnPerm homega heta hdegree (seed.inputState layer x)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.selected_activeReturnState_bne seed layer x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.firstReturn_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma firstReturn_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart) :
-- imply
  let mask := seed.retieMask layer let swapped := fkMedialBlackDartMaskSwap mask dart (finiteFirstReturn (fkMedialBlackBoundaryPerm (seed.targetPairing layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 = (finiteFirstReturn (alignedBoundaryPerm homega heta hdegree layer) (activeBlackDart (omega := omega) (eta := eta)) ⟨swapped, (activeBlackDart_maskSwap_iff mask dart).mpr hactive⟩).1 := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.firstReturn_active seed layer dart hactive

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.firstReturn_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma firstReturn_slot_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {dart : FKMedialBlackDart T}
-- given
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
  (hslot : fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer) dart = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) :
-- imply
  fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer) ((finiteFirstReturn (fkMedialBlackBoundaryPerm (seed.targetPairing layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1) = (doubledAlignedVertex (seed.activeReturnState layer x), doubledAlignedSlot homega heta hdegree layer (seed.activeReturnState layer x)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.firstReturn_slot seed layer x dart hactive hslot

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.targetBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma targetBoundary_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool} :
-- imply
  fkColoredStrandSlotBoundaryPerm (seed.targetPairing layer) = (fkColoredParityMaskStrandSlotSwap (seed.retieMask layer) false).trans ((fkColoredStrandSlotBoundaryPerm (alignedRoutingLoopPairing homega heta hdegree layer)).trans (fkColoredParityMaskStrandSlotSwap (seed.retieMask layer) true)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.targetBoundary seed layer

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_recover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma targetPairing_recover_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool} :
-- imply
  fkMedialTogglePairingMask (seed.targetPairing layer) (seed.retieMask layer) = alignedRoutingLoopPairing homega heta hdegree layer := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_recover seed layer

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma retieMask_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (hzero : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 0) :
-- imply
  seed.retieMask layer v = false := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.retieMask_inactive seed layer v hzero

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma targetPairing_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (hzero : (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega v) (sixVertexLocalIncomingPattern eta v)).card = 0) :
-- imply
  seed.targetPairing layer v = alignedRoutingLoopPairing homega heta hdegree layer v := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.targetPairing_inactive seed layer v hzero

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_dart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transportedColor_dart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {dart : FKMedialBlackDart T} :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) = if _hdart : dart ∈ doubledAlignedBoundarySegments homega heta hdegree false seed.splitStates then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (!layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree (!layer) dart) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_dart seed layer dart

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transportedColor_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta} :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) = if _hx : x ∈ seed.splitStates then fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (!layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree (!layer) x) else fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_active seed layer x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedActiveColor_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transportedActiveColor_eq_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta} :
-- imply
  seed.transportedActiveColor layer x = if _hx : x ∈ seed.splitStates then sixVertexDegreeTwoAlignedActiveColor homega heta hdegree (!layer) x else sixVertexDegreeTwoAlignedActiveColor homega heta hdegree layer x := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedActiveColor_eq seed layer x

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_firstReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transportedColor_firstReturn_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {x : DoubledAlignedState omega eta}
  {dart : FKMedialBlackDart T}
-- given
  (hreturn : seed.ActiveReturnColorInvariant)
  (hactive : activeBlackDart (omega := omega) (eta := eta) dart)
  (hslot : fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer) dart = (doubledAlignedVertex x, doubledAlignedSlot homega heta hdegree layer x)) :
-- imply
  let arrival := (finiteFirstReturn (fkMedialBlackBoundaryPerm (seed.targetPairing layer)) (activeBlackDart (omega := omega) (eta := eta)) ⟨dart, hactive⟩).1 fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer) arrival)) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, fkColoredBlackDartStrandSlotEquiv (seed.targetPairing layer) dart)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_firstReturn seed hreturn layer x dart hactive hslot

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_dart_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transportedColor_dart_of_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta) dart) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_dart_of_inactive seed layer dart hinactive

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_falseBoundary_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma transportedColor_falseBoundary_of_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (hinactive : ¬ activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart)) :
-- imply
  fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (alignedBoundaryPerm homega heta hdegree false dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart)) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.transportedColor_falseBoundary_of_inactive seed layer dart hinactive

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.boundaryFalseDart_of_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma boundaryFalseDart_of_inactive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {dart : FKMedialBlackDart T}
-- given
  (hdart : ¬ activeBlackDart (omega := omega) (eta := eta) dart)
  (hnext : ¬ activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart)) :
-- imply
  seed.boundaryFalseDart layer dart = alignedBoundaryPerm homega heta hdegree false dart := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.boundaryFalseDart_of_inactive seed layer dart hdart hnext

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.targetBoundary_slotOfFalseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma targetBoundary_slotOfFalseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
  {layer : Bool}
  {dart : FKMedialBlackDart T} :
-- imply
  fkColoredStrandSlotBoundaryPerm (seed.targetPairing layer) (sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart) = sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (seed.boundaryFalseDart layer dart) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.targetBoundary_slotOfFalseDart seed layer dart

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.slotColorInvariant_of_falseDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma slotColorInvariant_of_falseDart_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hfalseDart : ∀ (layer : Bool) (dart : FKMedialBlackDart T), fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (seed.boundaryFalseDart layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart))) :
-- imply
  FKColoredIndexedOccurrenceSlotColorInvariant (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) seed.targetPairing (Fintype.card (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.slotColorInvariant_of_falseDart seed hfalseDart

/--
[SixVertexDegreeTwoSynchronizedHighChargeSeed.slotColorInvariant_of_active](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma slotColorInvariant_of_active_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {homega : omega.IceRule}
  {heta : eta.IceRule}
  {hdegree : SixVertexLocallyDegreeTwo omega eta}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {seed : SixVertexDegreeTwoSynchronizedHighChargeSeed homega heta hdegree component}
-- given
  (hactive : ∀ (layer : Bool) (dart : FKMedialBlackDart T), activeBlackDart (omega := omega) (eta := eta) dart ∨ activeBlackDart (omega := omega) (eta := eta) (alignedBoundaryPerm homega heta hdegree false dart) -> fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer (seed.boundaryFalseDart layer dart))) = fkColoredLayeredSlotColor (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) (seed.occurrenceEquiv (layer, sixVertexDegreeTwoAlignedBoundarySlotOfFalseDart homega heta hdegree layer dart))) :
-- imply
  FKColoredIndexedOccurrenceSlotColorInvariant (sixVertexDegreeTwoAlignedColoredSource homega heta hdegree) seed.targetPairing (Fintype.card (SixVertexDegreeTwoSynchronizedSplitBoundaryOccurrence seed)) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey seed) (sixVertexDegreeTwoSynchronizedSplitBoundaryFinKey_injective seed) := by
-- proof
  apply StatMech.FrontierD.SixVertexDegreeTwoSynchronizedHighChargeSeed.slotColorInvariant_of_active seed hactive

/--
[sum_sixVertexDegreeTwoSynchronizedComponentCharge_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sum_sixVertexDegreeTwoSynchronizedComponentCharge_eq_two_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  (∑ component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent, sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component) = 2 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexDegreeTwoSynchronizedComponentCharge_eq_two homega heta hdegree middle homegaSector hetaSector hmiddle

/--
[sixVertexDegreeTwoSynchronizedTotalComponentCharge_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedTotalComponentCharge_eq_two_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  sixVertexDegreeTwoSynchronizedTotalComponentCharge homega heta hdegree = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedTotalComponentCharge_eq_two homega heta hdegree middle homegaSector hetaSector hmiddle

/--
[sixVertexDegreeTwoSynchronizedComponent_predecessors_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponent_predecessors_iff_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk (sixVertexDegreeTwoBranchPredecessor homega heta hdegree false d) = component ↔ (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).connectedComponentMk (sixVertexDegreeTwoBranchPredecessor homega heta hdegree true d) = component := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponent_predecessors_iff homega heta hdegree component d

/--
[sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (∃ component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent, sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component = 1) \/ (∀ component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent, sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component ≠ 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponent_unit_or_fractional homega heta hdegree

/--
[sixVertexDegreeTwoSynchronizedComponent_halfFlow_charge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedComponent_halfFlow_charge_one_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  (∑ component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent, (sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component : ℚ) * (1 / 2)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedComponent_halfFlow_charge_one homega heta hdegree middle homegaSector hetaSector hmiddle

/--
[exists_sixVertexDegreeTwoSynchronizedComponentCharge_eq_one_of_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma exists_sixVertexDegreeTwoSynchronizedComponentCharge_eq_one_of_le_one_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hle : ∀ component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent, sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component ≤ 1) :
-- imply
  ∃ component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent, sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component = 1 := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexDegreeTwoSynchronizedComponentCharge_eq_one_of_le_one homega heta hdegree middle homegaSector hetaSector hmiddle hle

/--
[exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (hnoUnit : ∀ component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent, sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component ≠ 1) :
-- imply
  ∃ component : (sixVertexDegreeTwoSynchronizedGraph homega heta hdegree).ConnectedComponent, 2 ≤ sixVertexDegreeTwoSynchronizedComponentCharge homega heta hdegree component := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexDegreeTwoSynchronizedComponentCharge_ge_two_of_no_unit homega heta hdegree middle homegaSector hetaSector hmiddle hnoUnit

/--
[sixVertexDegreeTwoSynchronizedReconnectionSeed_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedComponents.lean)
-/
@[path]
private lemma sixVertexDegreeTwoSynchronizedReconnectionSeed_nonempty_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {middle : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = middle - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle) :
-- imply
  Nonempty (SixVertexDegreeTwoSynchronizedReconnectionSeed homega heta hdegree) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoSynchronizedReconnectionSeed_nonempty homega heta hdegree middle homegaSector hetaSector hmiddle


-- created on 2026-10-23

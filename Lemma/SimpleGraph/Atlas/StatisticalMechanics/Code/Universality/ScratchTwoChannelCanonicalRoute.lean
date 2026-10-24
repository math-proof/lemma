import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.ScratchTwoChannelCanonicalRoute
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_connectorCentralFacePIMSConfig_congr_of_centralEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_connectorCentralFacePIMSConfig_congr_of_centralEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho sigma : ConfigSpace (Sym2 (RlcConnectorVertex n))}
-- given
  (hcentral : ∀ (e : Sym2 (Site 2)) (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma'), rho (rlc_connectorCentralFaceEdgeLift e he) = sigma (rlc_connectorCentralFaceEdgeLift e he)) :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' rho = rlc_connectorCentralFacePIMSConfig gamma gamma' sigma := by
-- proof
  apply StatMech.Universality.rlc_connectorCentralFacePIMSConfig_congr_of_centralEdges hcentral

/--
[rlc_twoChannel_centralBits_eq_of_PIMS_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannel_centralBits_eq_of_PIMS_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho sigma : ConfigSpace (Sym2 (RlcConnectorVertex n))}
  {source : (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet}
-- given
  (hcover : RlcTwoChannelPIMSCoversCentralEdges gamma gamma')
  (hpims : rlc_connectorCentralFacePIMSConfig gamma gamma' rho = rlc_connectorCentralFacePIMSConfig gamma gamma' sigma) :
-- imply
  rho source.1 = sigma source.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_centralBits_eq_of_PIMS_eq hcover hpims source

/--
[rlc_twoChannel_PIMS_and_discardedBits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannel_PIMS_and_discardedBits_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hcover : RlcTwoChannelPIMSCoversCentralEdges gamma gamma') :
-- imply
  Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' => (rlc_connectorCentralFacePIMSConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega), fun e : RlcTwoChannelDiscardedEdge gamma gamma' => omega e.1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_PIMS_and_discardedBits_injective hcover

/--
[rlc_twoChannelPIMSSourceEdge_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSSourceEdge_map_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'} :
-- imply
  (rlc_twoChannelPIMSSourceEdge target).1.map Subtype.val = rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSSourceEdge_map target

/--
[rlc_twoChannelPIMSSourceEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSSourceEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_twoChannelPIMSSourceEdge (gamma := gamma) (gamma' := gamma')) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSSourceEdge_injective

/--
[rlc_twoChannelPIMSSourceEdge_mem_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSSourceEdge_mem_central_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'} :
-- imply
  (rlc_twoChannelPIMSSourceEdge target).1 ∈ (rlc_connectorCentralFaceFiniteGraph gamma gamma').edgeSet := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSSourceEdge_mem_central target

/--
[rlc_twoChannelPIMSEdgePerm_variable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSEdgePerm_variable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelPIMSEdgePerm gamma gamma' e.1 = rlc_twoChannelPIMSSourceEdge e := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSEdgePerm_variable e

/--
[rlc_twoChannelFullPIMSConfig_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelFullPIMSConfig_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_twoChannelFullPIMSConfig gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPIMSConfig_injective

/--
[rlc_twoChannelPIMSConfig_variableTarget_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSConfig_variableTarget_apply_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {target : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'} :
-- imply
  rlc_connectorCentralFacePIMSConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) target.1.1 = !(omega (rlc_twoChannelPIMSSourceEdge target)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSConfig_variableTarget_apply omega target

/--
[rlc_twoChannel_PIMS_and_exactDiscardedBits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannel_PIMS_and_exactDiscardedBits_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' => (rlc_connectorCentralFacePIMSConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega), fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' => omega e.1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_PIMS_and_exactDiscardedBits_injective

/--
[rlc_twoChannelPIMSEdgeProjection_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSEdgeProjection_apply_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet} :
-- imply
  rlc_twoChannelPIMSEdgeProjection gamma gamma' omega e = rlc_connectorCentralFacePIMSConfig gamma gamma' (rlc_twoChannelEdgeConfigExtend gamma gamma' omega) e.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSEdgeProjection_apply omega e

/--
[rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (fun omega : RlcTwoChannelEdgeConfig gamma gamma' => (rlc_twoChannelPIMSEdgeProjection gamma gamma' omega, fun e : RlcTwoChannelPIMSDiscardedSourceEdge gamma gamma' => omega e.1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_PIMSEdgeProjection_and_exactDiscardedBits_injective

/--
[rlc_twoChannelPIMSEdgeProjection_fixedTarget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSEdgeProjection_fixedTarget_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho sigma : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : RlcTwoChannelPIMSFixedTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelPIMSEdgeProjection gamma gamma' rho e.1 = rlc_twoChannelPIMSEdgeProjection gamma gamma' sigma e.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSEdgeProjection_fixedTarget_eq rho sigma e

/--
[rlc_twoChannelFullPIMSConfig_variable_eq_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelFullPIMSConfig_variable_eq_projection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelFullPIMSConfig gamma gamma' omega e.1 = rlc_twoChannelPIMSEdgeProjection gamma gamma' omega e.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPIMSConfig_variable_eq_projection omega e

/--
[rlc_mem_twoChannelOpenEdgeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_mem_twoChannelOpenEdgeSet_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet} :
-- imply
  e ∈ rlc_twoChannelOpenEdgeSet omega ↔ omega e = true := by
-- proof
  apply StatMech.Universality.rlc_mem_twoChannelOpenEdgeSet_iff omega e

/--
[rlc_twoChannelSuccessfulSubconfigs_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelSuccessfulSubconfigs_nonempty_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : RlcTwoChannelEdgeSuccess gamma gamma'} :
-- imply
  (rlc_twoChannelSuccessfulSubconfigs eta).Nonempty := by
-- proof
  apply StatMech.Universality.rlc_twoChannelSuccessfulSubconfigs_nonempty eta

/--
[rlc_twoChannelCanonicalRoute_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelCanonicalRoute_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : RlcTwoChannelEdgeSuccess gamma gamma'} :
-- imply
  rlc_twoChannelCanonicalRoute eta ∈ rlc_twoChannelSuccessfulSubconfigs eta := by
-- proof
  apply StatMech.Universality.rlc_twoChannelCanonicalRoute_mem eta

/--
[rlc_twoChannelCanonicalRoute_open_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelCanonicalRoute_open_subset_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : RlcTwoChannelEdgeSuccess gamma gamma'} :
-- imply
  rlc_twoChannelOpenEdgeSet (rlc_twoChannelCanonicalRoute eta).1 ⊆ rlc_twoChannelOpenEdgeSet eta.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelCanonicalRoute_open_subset eta

/--
[rlc_twoChannelCanonicalRoute_target_mem_codeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelCanonicalRoute_target_mem_codeSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {eta : RlcTwoChannelEdgeSuccess gamma gamma'} :
-- imply
  eta.1 ∈ (rlc_twoChannelCanonicalRoutePlan gamma gamma').codeSet (rlc_twoChannelCanonicalRoute eta) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelCanonicalRoute_target_mem_codeSet eta

/--
[rlc_twoChannelCanonicalRoute_target_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelCanonicalRoute_target_compatible_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelEdgeFailure gamma gamma' → RlcTwoChannelEdgeSuccess gamma gamma'}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'} :
-- imply
  (rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible (rlc_twoChannelCanonicalRouteAvailable target) rho (target rho) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelCanonicalRoute_target_compatible target rho

/--
[RlcTwoChannelCanonicalFibrePacking.embedding_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma embedding_compatible_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelEdgeFailure gamma gamma' → RlcTwoChannelEdgeSuccess gamma gamma'}
  {packing : RlcTwoChannelCanonicalFibrePacking target}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'} :
-- imply
  (rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible (rlc_twoChannelCanonicalRouteAvailable target) rho (packing.embedding rho) := by
-- proof
  apply StatMech.Universality.RlcTwoChannelCanonicalFibrePacking.embedding_compatible packing rho

/--
[RlcTwoChannelCanonicalFibrePacking.hasCodeHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma hasCodeHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelEdgeFailure gamma gamma' → RlcTwoChannelEdgeSuccess gamma gamma'}
  {packing : RlcTwoChannelCanonicalFibrePacking target} :
-- imply
  (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall (rlc_twoChannelCanonicalRouteAvailable target) := by
-- proof
  apply StatMech.Universality.RlcTwoChannelCanonicalFibrePacking.hasCodeHall packing

/--
[rlc_twoChannelCanonicalRoute_hasCodeHall_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelCanonicalRoute_hasCodeHall_of_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelEdgeFailure gamma gamma' → RlcTwoChannelEdgeSuccess gamma gamma'}
-- given
  (htarget : Function.Injective target) :
-- imply
  (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall (rlc_twoChannelCanonicalRouteAvailable target) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelCanonicalRoute_hasCodeHall_of_injective target htarget

/--
[rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma') :
-- imply
  RlcCentralFaceClosureFailureCertificate gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence hinc

/--
[rlc_twoChannelPIMSEdgeTargetOfClosure_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSEdgeTargetOfClosure_val_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
-- imply
  (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 = rlc_twoChannelPIMSEdgeProjection gamma gamma' rho.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSEdgeTargetOfClosure_val hclosure rho

/--
[rlc_twoChannelCanonicalForcedFullPIMSConfig_variable_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelCanonicalForcedFullPIMSConfig_variable_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'}
  {e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
-- imply
  rlc_twoChannelCanonicalForcedFullPIMSConfig hclosure rho e.1 = (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelCanonicalForcedFullPIMSConfig_variable_eq hclosure rho e

/--
[rlc_twoChannelCanonicalForcedFullPIMSConfig_reserved_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelCanonicalForcedFullPIMSConfig_reserved_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'}
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (he : e ∈ rlc_twoChannelOpenEdgeSet (rlc_twoChannelCanonicalRoute (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1) :
-- imply
  rlc_twoChannelCanonicalForcedFullPIMSConfig hclosure rho e = true := by
-- proof
  apply StatMech.Universality.rlc_twoChannelCanonicalForcedFullPIMSConfig_reserved_open hclosure rho e he

/--
[rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_eq_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_eq_at_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
  {eta : RlcTwoChannelEdgeSuccess gamma gamma'}
  {rho : RlcTwoChannelTargetFibre (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure) eta}
-- given
  (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure) :
-- imply
  rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity rho.1 = rlc_twoChannelPIMSFixedPayloadConfigAt hcapacity eta rho := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_eq_at hcapacity eta rho

/--
[rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_variable_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_variable_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'}
  {e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'}
-- given
  (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure) :
-- imply
  rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity rho e.1 = (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho).1 e.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_variable_eq hcapacity rho e

/--
[rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_reserved_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_reserved_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'}
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hcapacity : RlcTwoChannelPIMSFixedPayloadCapacity hclosure)
  (he : e ∈ rlc_twoChannelOpenEdgeSet (rlc_twoChannelCanonicalRoute (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho)).1) :
-- imply
  rlc_twoChannelPIMSFixedPayloadConfigOfCapacity hcapacity rho e = true := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSFixedPayloadConfigOfCapacity_reserved_open hcapacity rho e he

/--
[RlcTwoChannelPIMSDiscardedPayloadPacking.target_eq_of_pack_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma target_eq_of_pack_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
  {packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure}
  {rho sigma : RlcTwoChannelEdgeFailure gamma gamma'}
-- given
  (hpack : packing.packConfig rho = packing.packConfig sigma) :
-- imply
  rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho = rlc_twoChannelPIMSEdgeTargetOfClosure hclosure sigma := by
-- proof
  apply StatMech.Universality.RlcTwoChannelPIMSDiscardedPayloadPacking.target_eq_of_pack_eq packing hpack

/--
[RlcTwoChannelPIMSDiscardedPayloadPacking.packConfig_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma packConfig_success_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
  {packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'} :
-- imply
  rlc_twoChannelEdgeConfigExtend gamma gamma' (packing.packConfig rho) ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcTwoChannelPIMSDiscardedPayloadPacking.packConfig_success packing rho

/--
[RlcTwoChannelPIMSDiscardedPayloadPacking.embedding_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma embedding_compatible_eq_2
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
  {packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'} :
-- imply
  (rlc_twoChannelCanonicalRoutePlan gamma gamma').Compatible (rlc_twoChannelCanonicalRouteAvailable (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure)) rho (packing.embedding rho) := by
-- proof
  apply StatMech.Universality.RlcTwoChannelPIMSDiscardedPayloadPacking.embedding_compatible packing rho

/--
[RlcTwoChannelPIMSDiscardedPayloadPacking.hasCodeHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma hasCodeHall_eq_2
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
  {packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure} :
-- imply
  (rlc_twoChannelCanonicalRoutePlan gamma gamma').HasCodeHall (rlc_twoChannelCanonicalRouteAvailable (rlc_twoChannelPIMSEdgeTargetOfClosure hclosure)) := by
-- proof
  apply StatMech.Universality.RlcTwoChannelPIMSDiscardedPayloadPacking.hasCodeHall packing

/--
[RlcTwoChannelPIMSDiscardedPayloadPacking.recoverBase_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma recoverBase_embedding_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma'}
  {packing : RlcTwoChannelPIMSDiscardedPayloadPacking hclosure}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'} :
-- imply
  packing.recoverBase (packing.embedding rho) = rlc_twoChannelPIMSEdgeTargetOfClosure hclosure rho := by
-- proof
  apply StatMech.Universality.RlcTwoChannelPIMSDiscardedPayloadPacking.recoverBase_embedding packing rho

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulCanonicalPIMSRouteHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulCanonicalPIMSRouteHall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma')
  (hHall : RlcBookFaithfulCanonicalPIMSRouteHall hinc) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulCanonicalPIMSRouteHall hinc hHall

/--
[rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulPIMSFibrePacking](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ScratchTwoChannelCanonicalRoute.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulPIMSFibrePacking_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {packing : RlcTwoChannelCanonicalFibrePacking (rlc_twoChannelPIMSEdgeTargetOfClosure (rlc_twoChannelClosureFailureCertificate_of_centralFace gamma gamma' (rlc_centralFaceClosureFailureCertificate_of_retainedAnchorIncidence hinc)))}
-- given
  (hinc : RlcBookFaithfulRetainedAnchorIncidence gamma gamma') :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ ≤ FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (1 / 2) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_merged_q_one_of_faithfulPIMSFibrePacking hinc packing


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part86
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_twoChannelFullPhysicalSourceEdge_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalSourceEdge_map_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'} :
-- imply
  (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val = rlc_pimsEdgeEquiv (target.1.1.map Subtype.val) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalSourceEdge_map target

/--
[rlc_twoChannelFullPhysicalSourceEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalSourceEdge_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_twoChannelFullPhysicalSourceEdge (gamma := gamma) (gamma' := gamma')) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalSourceEdge_injective

/--
[rlc_twoChannelFullPhysicalSourceEdge_targetOfVisibleSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalSourceEdge_targetOfVisibleSource_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma'} :
-- imply
  rlc_twoChannelFullPhysicalSourceEdge (rlc_twoChannelFullPhysicalTargetOfVisibleSource source) = source.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalSourceEdge_targetOfVisibleSource source

/--
[rlc_twoChannelFullPhysicalEdgePerm_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalEdgePerm_physical_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelFullPhysicalEdgePerm gamma gamma' target.1 = rlc_twoChannelFullPhysicalSourceEdge target := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalEdgePerm_physical target

/--
[rlc_twoChannelFullPhysicalPermConfig_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_injective_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  Function.Injective (rlc_twoChannelFullPhysicalPermConfig gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_injective

/--
[rlc_twoChannelFullPhysicalPermConfig_eq_fullDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_eq_fullDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega target.1 = rlc_twoChannelFullDualConfig gamma gamma' omega target.1.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_eq_fullDual omega target

/--
[rlc_twoChannelFullPhysicalPermConfig_targetOfVisibleSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_targetOfVisibleSource_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma'} :
-- imply
  rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega (rlc_twoChannelFullPhysicalTargetOfVisibleSource source).1 = !(omega source.1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_targetOfVisibleSource omega source

/--
[rlc_twoChannelFullPhysicalPermConfig_success_of_variableConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_success_of_variableConnector_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hvariable : RlcTwoChannelFullVariableConnectorSuccess gamma gamma' omega) :
-- imply
  rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_success_of_variableConnector omega hvariable

/--
[rlc_twoChannelFullPhysical_not_visibleSourceConnector_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_not_visibleSourceConnector_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ¬RlcTwoChannelFullPhysicalVisibleSourceConnectorSuccess gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_not_visibleSourceConnector_of_failure omega hno

/--
[rlc_twoChannelFullPhysical_right_mem_visibleRightReachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_right_mem_visibleRightReachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x : RlcConnectorVertex n}
-- given
  (hx : rlc_connectorOnRight gamma x) :
-- imply
  x ∈ rlc_twoChannelFullPhysicalVisibleRightReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_right_mem_visibleRightReachSet omega hx

/--
[rlc_twoChannelFullPhysical_left_not_mem_visibleRightReachSet_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_left_not_mem_visibleRightReachSet_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {y : RlcConnectorVertex n}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hy : rlc_connectorOnLeft gamma' y) :
-- imply
  y ∉ rlc_twoChannelFullPhysicalVisibleRightReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_left_not_mem_visibleRightReachSet_of_failure omega hno hy

/--
[rlc_twoChannelFullPhysical_visibleSource_closed_of_crosses_reachSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_visibleSource_closed_of_crosses_reachSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma'}
  {u v : RlcConnectorVertex n}
-- given
  (hsource : source.1.1 = s(u, v))
  (hcross : (u ∈ rlc_twoChannelFullPhysicalVisibleRightReachSet gamma gamma' omega ∧ v ∉ rlc_twoChannelFullPhysicalVisibleRightReachSet gamma gamma' omega) ∨ (v ∈ rlc_twoChannelFullPhysicalVisibleRightReachSet gamma gamma' omega ∧ u ∉ rlc_twoChannelFullPhysicalVisibleRightReachSet gamma gamma' omega)) :
-- imply
  omega source.1 = false := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_visibleSource_closed_of_crosses_reachSet omega source hsource hcross

/--
[rlc_twoChannelFullPhysicalLiftVertexCut_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalLiftVertexCut_mem_eq
  {n : Int}
  {A : Set (RlcConnectorVertex n)}
  {x : RlcConnectorVertex n} :
-- imply
  x.1 ∈ rlc_twoChannelFullPhysicalLiftVertexCut A ↔ x ∈ A := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalLiftVertexCut_mem A x

/--
[rlc_twoChannel_traceWiring_not_crosses_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannel_traceWiring_not_crosses_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u v : RlcConnectorVertex n}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (htrace : (rlc_connectorTraceWiring gamma gamma').Adj u v) :
-- imply
  ¬((u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_traceWiring_not_crosses_staticCut gamma gamma' A hAright hAleft htrace

/--
[rlc_twoChannel_augmented_crossing_mem_twoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannel_augmented_crossing_mem_twoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u v : RlcConnectorVertex n}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (haug : (rlc_connectorTwoChannelAugmentedPlanarDomain gamma gamma').G.Adj u v)
  (hcross : (u ∈ A ∧ v ∉ A) ∨ (v ∈ A ∧ u ∉ A)) :
-- imply
  (rlc_connectorTwoChannelGraph gamma gamma').Adj u v := by
-- proof
  apply StatMech.Universality.rlc_twoChannel_augmented_crossing_mem_twoChannel gamma gamma' A hAright hAleft haug hcross

/--
[rlc_twoChannelFullPhysicalCutTargetGraphAt_adj_iff_faceBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalCutTargetGraphAt_adj_iff_faceBoundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {x y : RlcConnectorVertex n} :
-- imply
  (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Adj x y ↔ ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', target.1.1 = s(x, y) ∧ (faceBoundaryGraph (rlc_twoChannelFullPhysicalLiftVertexCut A)).Adj (rlc_dualReflect.symm x.1) (rlc_dualReflect.symm y.1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalCutTargetGraphAt_adj_iff_faceBoundary gamma gamma' A x y

/--
[rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_variable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_variable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullPhysicalVisibleCutTargetGraph gamma gamma' omega ≤ rlc_twoChannelFullVariableGraph gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_variable gamma gamma' omega

/--
[rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_open_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullPhysicalVisibleCutTargetGraph gamma gamma' omega ≤ FK.openSub (rlc_connectorTwoChannelGraph gamma gamma') (rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_open gamma gamma' omega

/--
[rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_openFullDual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_openFullDual_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullPhysicalVisibleCutTargetGraph gamma gamma' omega ≤ FK.openSub (rlc_twoChannelFullVariableGraph gamma gamma') (rlc_twoChannelFullDualConfig gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalVisibleCutTargetGraph_le_openFullDual gamma gamma' omega

/--
[rlc_twoChannelFullPhysicalPermConfig_success_of_visibleCutTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_success_of_visibleCutTarget_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hcut : RlcTwoChannelFullPhysicalVisibleCutTargetConnectorSuccess gamma gamma' omega) :
-- imply
  rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_success_of_visibleCutTarget omega hcut

/--
[rlc_twoChannelFullVariableConnectorSuccess_of_visibleCutTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullVariableConnectorSuccess_of_visibleCutTarget_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hcut : RlcTwoChannelFullPhysicalVisibleCutTargetConnectorSuccess gamma gamma' omega) :
-- imply
  RlcTwoChannelFullVariableConnectorSuccess gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullVariableConnectorSuccess_of_visibleCutTarget omega hcut

/--
[rlc_reachable_between_of_odd_degree_blocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_reachable_between_of_odd_degree_blocks_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred R]
-- given
  (R L : V → Prop)
  (hoddSupport : ∀ v, Odd (G.degree v) → R v ∨ L v)
  (hRodd : Odd (Fintype.card {v : V // R v ∧ Odd (G.degree v)})) :
-- imply
  ∃ r l, R r ∧ L l ∧ G.Reachable r l := by
-- proof
  apply StatMech.Universality.rlc_reachable_between_of_odd_degree_blocks G R L hoddSupport hRodd

/--
[rlc_twoChannelFullPhysicalCutInteriorConfig_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalCutInteriorConfig_true_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {e : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet} :
-- imply
  rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A e = true ↔ ∀ u v : RlcConnectorVertex n, e.1 = s(u, v) → u ∈ A ∧ v ∈ A := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalCutInteriorConfig_true_iff gamma gamma' A e

/--
[rlc_twoChannelFullPhysicalCutInteriorConfig_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalCutInteriorConfig_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
-- imply
  rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalCutInteriorConfig_failure gamma gamma' A hAright hAleft

/--
[rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic_eq
  {A : Set V}
  {e : Sym2 V} :
-- imply
  ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A e ↔ PairedEdgeMonochromatic A e := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_not_crossesCut_iff_monochromatic A e

/--
[pairedEdgeCutIntersection_iff_twoColorHexAlternative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma pairedEdgeCutIntersection_iff_twoColorHexAlternative_eq
  {source target : I → Sym2 V}
  {R L : Set V} :
-- imply
  PairedEdgeCutIntersection source target R L ↔ PairedEdgeTwoColorHexAlternative source target R L := by
-- proof
  apply StatMech.Universality.pairedEdgeCutIntersection_iff_twoColorHexAlternative source target R L

/--
[pairedEdgeCutIntersection_of_hexCutCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma pairedEdgeCutIntersection_of_hexCutCarrier_eq
  {source target : I → Sym2 V}
  {R L : Set V}
-- given
  (hcarrier : ∀ A B : Set V, R ⊆ A → L ∩ A = ∅ → R ⊆ B → L ∩ B = ∅ → Nonempty (PairedEdgeHexCutCarrier source target A B)) :
-- imply
  PairedEdgeCutIntersection source target R L := by
-- proof
  apply StatMech.Universality.pairedEdgeCutIntersection_of_hexCutCarrier source target R L hcarrier

/--
[rlc_twoChannelFullPhysicalStaticCutIntersection_iff_pairedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutIntersection_iff_pairedEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith ↔ PairedEdgeCutIntersection (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦ (rlc_twoChannelFullPhysicalSourceEdge target).1) (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦ target.1.1) {x | rlc_connectorOnRight gamma x} {x | rlc_connectorOnLeft gamma' x} := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutIntersection_iff_pairedEdge hfaith

/--
[rlc_twoChannelFullPhysicalStaticCutIntersection_iff_twoColorHex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutIntersection_iff_twoColorHex_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith ↔ PairedEdgeTwoColorHexAlternative (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦ (rlc_twoChannelFullPhysicalSourceEdge target).1) (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦ target.1.1) {x | rlc_connectorOnRight gamma x} {x | rlc_connectorOnLeft gamma' x} := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutIntersection_iff_twoColorHex hfaith

/--
[rlc_twoChannelFullPhysicalStaticCutIntersection_of_hexCutCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutIntersection_of_hexCutCarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hcarrier : ∀ A B : Set (RlcConnectorVertex n), {x | rlc_connectorOnRight gamma x} ⊆ A → {x | rlc_connectorOnLeft gamma' x} ∩ A = ∅ → {x | rlc_connectorOnRight gamma x} ⊆ B → {x | rlc_connectorOnLeft gamma' x} ∩ B = ∅ → Nonempty (PairedEdgeHexCutCarrier (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦ (rlc_twoChannelFullPhysicalSourceEdge target).1) (fun target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' ↦ target.1.1) A B)) :
-- imply
  RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutIntersection_of_hexCutCarrier hfaith hcarrier

/--
[rlc_twoChannelFullPhysicalStaticCutIntersection_of_odd_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutIntersection_of_odd_intersection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hodd : ∀ A B : Set (RlcConnectorVertex n), (∀ x, rlc_connectorOnRight gamma x → x ∈ A) → (∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) → (∀ x, rlc_connectorOnRight gamma x → x ∈ B) → (∀ y, rlc_connectorOnLeft gamma' y → y ∉ B) → Odd (rlc_twoChannelFullPhysicalCutIntersectionTargets gamma gamma' A B).card) :
-- imply
  RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutIntersection_of_odd_intersection hfaith hodd

/--
[rlc_twoChannelFullPhysicalStaticCutConnectivity_of_cutIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutConnectivity_of_cutIntersection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hintersect : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutConnectivity_of_cutIntersection hfaith hintersect

/--
[rlc_twoChannelFullPhysicalStaticCutIntersection_of_cutConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutIntersection_of_cutConnectivity_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hconnect : RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutIntersection_of_cutConnectivity hfaith hconnect

/--
[rlc_twoChannelFullPhysicalStaticCutConnectivity_iff_cutIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutConnectivity_iff_cutIntersection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith ↔ RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutConnectivity_iff_cutIntersection hfaith

/--
[rlc_twoChannelFullPhysicalVisibleCutDuality_of_staticCutConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalVisibleCutDuality_of_staticCutConnectivity_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalVisibleCutDuality gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalVisibleCutDuality_of_staticCutConnectivity hfaith hstatic

/--
[rlc_twoChannelFullPhysicalPermutationSuccess_of_visibleCutDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermutationSuccess_of_visibleCutDuality_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hduality : RlcTwoChannelFullPhysicalVisibleCutDuality gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermutationSuccess_of_visibleCutDuality hfaith hduality

/--
[rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hintersect : RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermutationSuccess_of_staticCutIntersection hfaith hintersect

/--
[rlc_twoChannelFullVariableFailureDuality_of_visibleCutDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullVariableFailureDuality_of_visibleCutDuality_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hduality : RlcTwoChannelFullPhysicalVisibleCutDuality gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullVariableFailureDuality gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullVariableFailureDuality_of_visibleCutDuality hfaith hduality

/--
[rlc_twoChannelFullVariableFailureDuality_of_visiblePlanarDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullVariableFailureDuality_of_visiblePlanarDuality_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hplanar : RlcTwoChannelFullPhysicalVisiblePlanarDuality gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullVariableFailureDuality gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullVariableFailureDuality_of_visiblePlanarDuality hfaith hplanar

/--
[rlc_twoChannelFullPhysicalPermutationSuccess_of_visiblePlanarDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermutationSuccess_of_visiblePlanarDuality_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hplanar : RlcTwoChannelFullPhysicalVisiblePlanarDuality gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermutationSuccess_of_visiblePlanarDuality hfaith hplanar

/--
[rlc_twoChannelFullPhysicalPermutationSuccess_of_variableFailureDuality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermutationSuccess_of_variableFailureDuality_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hduality : RlcTwoChannelFullVariableFailureDuality gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermutationSuccess_of_variableFailureDuality hfaith hduality

/--
[rlc_twoChannelFullPhysicalSuccessEmbedding_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalSuccessEmbedding_compatible_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith) :
-- imply
  RlcTwoChannelPIMSPooledVisibleCompatible hclosure rho (rlc_twoChannelFullPhysicalSuccessEmbedding hfaith hphysical rho) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalSuccessEmbedding_compatible hclosure hfaith hphysical rho

/--
[rlc_twoChannelPIMSPooledScoreHall_of_fullPhysicalSuccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSPooledScoreHall_of_fullPhysicalSuccess_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {N : Nat}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  RlcTwoChannelEdgeCodeHall gamma gamma' (RlcTwoChannelPIMSPooledScoreCompatible hclosure N) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSPooledScoreHall_of_fullPhysicalSuccess hclosure hfaith hphysical N hscore

/--
[rlc_twoChannelFullPhysicalPermConfig_success_of_supportedWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_success_of_supportedWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {walk : (openSubgraph 2 (rlc_dualReflectConfig (rlc_twoChannelFullAmbientConfig gamma gamma' omega))).Walk x y}
-- given
  (hx : x ∈ rlc_pathVertices gamma.1)
  (hy : y ∈ rlc_pathVertices gamma'.1)
  (hsupported : ∀ e ∈ walk.edges, ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', target.1.1.map Subtype.val = e) :
-- imply
  rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_success_of_supportedWalk omega hx hy walk hsupported

/--
[rlc_twoChannelFullPhysicalGoodBoundaryGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalGoodBoundaryGraph_le_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega ≤ faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega

/--
[rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2} :
-- imply
  RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ↔ RlcTwoChannelFullPhysicalTargetCarrierLocal gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalTargetCarrierGeometry_iff_local gamma gamma' f g

/--
[rlc_twoChannelFullPhysicalSourceCarrierGeometry_iff_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalSourceCarrierGeometry_iff_local_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2} :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g ↔ RlcTwoChannelFullPhysicalSourceCarrierLocal gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalSourceCarrierGeometry_iff_local gamma gamma' f g

/--
[rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2} :
-- imply
  RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g ↔ RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ∧ RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_target_and_source gamma gamma' f g

/--
[rlc_twoChannelFullPhysical_boundaryCarrierGeometry_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundaryCarrierGeometry_comm_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g ↔ RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' g f := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundaryCarrierGeometry_comm gamma gamma' hfg

/--
[rlc_twoChannelFullPhysical_firstBad_eq_of_sharedSourceEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_firstBad_eq_of_sharedSourceEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {ur vr f g : Site 2}
-- given
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = sharedPrimalEdge ur vr)
  (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ur vr) :
-- imply
  s(f, g) = s(ur, vr) ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_firstBad_eq_of_sharedSourceEdge gamma gamma' hurv hfg hshared hbad

/--
[rlc_twoChannelFullPhysical_not_carrierGeometry_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_not_carrierGeometry_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2} :
-- imply
  ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g ↔ (¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ∨ ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_not_carrierGeometry_iff gamma gamma' f g

/--
[rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2} :
-- imply
  (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj f g ↔ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g ∧ RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_carrierGeometry gamma gamma' omega

/--
[rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_crossedVisible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_crossedVisible_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph S).Adj f g) :
-- imply
  RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g ↔ RlcTwoChannelFullPhysicalCrossedVisibleSourceGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalBoundaryCarrierGeometry_iff_crossedVisible gamma gamma' hfg

/--
[rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_crossedVisible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_crossedVisible_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2} :
-- imply
  (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj f g ↔ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g ∧ RlcTwoChannelFullPhysicalCrossedVisibleSourceGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalGoodBoundaryGraph_adj_iff_crossedVisible gamma gamma' omega

/--
[rlc_twoChannelFullPhysical_boundary_visibleSource_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_visibleSource_closed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
  {source : RlcTwoChannelFullPhysicalVisibleSourceEdge gamma gamma'}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hsource : source.1.1.map Subtype.val = sharedPrimalEdge f g) :
-- imply
  omega source.1 = false := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_visibleSource_closed gamma gamma' omega hfg source hsource

/--
[rlc_twoChannelFullPhysical_noGoodComponent_forbids_contactReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noGoodComponent_forbids_contactReachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noGoodComponent_forbids_contactReachable hnoGood hxPath hyPath

/--
[rlc_twoChannelFullPhysical_noGood_rightWalk_end_not_leftContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noGood_rightWalk_end_not_leftContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1) :
-- imply
  rlc_dualReflect u ∉ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noGood_rightWalk_end_not_leftContact hnoGood hxPath q

/--
[rlc_twoChannelFullPhysical_noGood_leftWalk_end_not_rightContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noGood_leftWalk_end_not_rightContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {y u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y u}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  rlc_dualReflect u ∉ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noGood_leftWalk_end_not_rightContact hnoGood hyPath q

/--
[rlc_twoChannelFullPhysical_badCarrierSeparation_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_badCarrierSeparation_split_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hbad : RlcTwoChannelFullPhysicalBadCarrierSeparation gamma gamma' omega) :
-- imply
  RlcTwoChannelFullPhysicalBadTargetSeparation gamma gamma' omega ∨ RlcTwoChannelFullPhysicalBadSourceSeparation gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_badCarrierSeparation_split hbad

/--
[rlc_twoChannelFullPhysical_goodComponent_or_badCarrierSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodComponent_or_badCarrierSeparation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨ RlcTwoChannelFullPhysicalBadCarrierSeparation gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodComponent_or_badCarrierSeparation gamma gamma' hfaith omega hno

/--
[rlc_twoChannelFullPhysical_goodComponent_or_badTarget_or_badSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodComponent_or_badTarget_or_badSource_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨ RlcTwoChannelFullPhysicalBadTargetSeparation gamma gamma' omega ∨ RlcTwoChannelFullPhysicalBadSourceSeparation gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodComponent_or_badTarget_or_badSource gamma gamma' hfaith omega hno

/--
[rlc_twoChannelFullFilledBoundary_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledBoundary_isCycles_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).IsCycles := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledBoundary_isCycles gamma gamma' omega

/--
[rlc_twoChannelFullReachSet_subset_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullReachSet_subset_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
-- imply
  rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ⊆ rlc_twoChannelFullPhysicalLiftVertexCut A := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullReachSet_subset_staticCut gamma gamma' A hAright hAleft

/--
[rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {f g : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj f g)
  (hcarrier : RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
-- imply
  ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', target.1.1.map Subtype.val = s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundaryCarrier_source_crosses_staticCut gamma gamma' A hAright hAleft hfg hcarrier

/--
[rlc_twoChannelFullPhysicalLiftFace_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalLiftFace_of_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {f : Site 2}
-- given
  (hf : rlc_dualReflect f ∈ rect (-2 * n) (2 * n) (-n) n) :
-- imply
  rlc_twoChannelFullPhysicalLiftFace gamma f = ⟨rlc_dualReflect f, hf⟩ := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalLiftFace_of_mem gamma f hf

/--
[rlc_twoChannelFullPhysical_goodBoundary_le_staticCutTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodBoundary_le_staticCutTarget_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
-- imply
  ∀ {f g : Site 2}, (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Adj f g → (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Adj (rlc_twoChannelFullPhysicalLiftFace gamma f) (rlc_twoChannelFullPhysicalLiftFace gamma g) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodBoundary_le_staticCutTarget gamma gamma' A hAright hAleft

/--
[rlc_twoChannelFullPhysical_goodBoundary_ne_reachableSourceCrossing_atCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodBoundary_ne_reachableSourceCrossing_atCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {f g p q : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hfg : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Adj f g)
  (hp : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hq : q ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hcross : sharedPrimalEdge f g = s(p, q)) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodBoundary_ne_reachableSourceCrossing_atCut gamma gamma' A hAright hAleft hfg hp hq hcross

/--
[rlc_twoChannelFullPhysical_reachableSource_goodBoundary_subdiv_disjoint_atCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachableSource_goodBoundary_subdiv_disjoint_atCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {a b f g : Site 2}
  {H : (hypercubicLattice 2).Walk a b}
  {V : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk f g}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hHReach : ∀ v ∈ H.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) :
-- imply
  ¬∃ z : Site 2, z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support ∧ z ∈ (StatMech.TwoDim.zfe_faceSubdiv ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))).support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachableSource_goodBoundary_subdiv_disjoint_atCut gamma gamma' A hAright hAleft H hHReach V

/--
[rlc_zfe_primalSubdiv_mem_doubledRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_zfe_primalSubdiv_mem_doubledRect_eq
  {a b : Site 2}
  {H : (hypercubicLattice 2).Walk a b}
  {left right bottom top : Int}
-- given
  (hH : ∀ z ∈ H.support, z ∈ rect left right bottom top) :
-- imply
  ∀ z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support, z ∈ rect (2 * left) (2 * right) (2 * bottom) (2 * top) := by
-- proof
  apply StatMech.Universality.rlc_zfe_primalSubdiv_mem_doubledRect H left right bottom top hH

/--
[rlc_zfe_faceSubdiv_mem_doubledRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_zfe_faceSubdiv_mem_doubledRect_eq
  {f g : Site 2}
  {V : (hypercubicLattice 2).Walk f g}
  {left right bottom top : Int}
-- given
  (hV : ∀ z ∈ V.support, z ∈ rect left right bottom top) :
-- imply
  ∀ z ∈ (StatMech.TwoDim.zfe_faceSubdiv V).support, z ∈ rect (2 * left + 1) (2 * right + 1) (2 * bottom + 1) (2 * top + 1) := by
-- proof
  apply StatMech.Universality.rlc_zfe_faceSubdiv_mem_doubledRect V left right bottom top hV

/--
[rlc_twoChannelFullPhysical_not_reachableSource_goodBoundary_transverse_atCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_not_reachableSource_goodBoundary_transverse_atCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {a b f g : Site 2}
  {H : (hypercubicLattice 2).Walk a b}
  {V : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk f g}
  {alpha beta bottom top : Int}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hHReach : ∀ v ∈ H.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hab : alpha < beta)
  (hbt : bottom ≤ top)
  (hHstartBox : StatMech.TwoDim.zfe_primalEmb a ∈ rect alpha beta bottom top)
  (hHendBox : StatMech.TwoDim.zfe_primalEmb b ∈ rect alpha beta bottom top)
  (hHstartLeft : StatMech.TwoDim.zfe_primalEmb a 0 = alpha)
  (hHendRight : StatMech.TwoDim.zfe_primalEmb b 0 = beta)
  (hHBox : ∀ z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support, z ∈ rect alpha beta bottom top)
  (hVstartBottom : StatMech.TwoDim.zfe_faceEmb f 1 = bottom)
  (hVendTop : StatMech.TwoDim.zfe_faceEmb g 1 = top)
  (hVstartX : alpha ≤ StatMech.TwoDim.zfe_faceEmb f 0 ∧ StatMech.TwoDim.zfe_faceEmb f 0 ≤ beta)
  (hVendX : alpha ≤ StatMech.TwoDim.zfe_faceEmb g 0 ∧ StatMech.TwoDim.zfe_faceEmb g 0 ≤ beta)
  (hVBox : ∀ z ∈ (StatMech.TwoDim.zfe_faceSubdiv ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))).support, z ∈ rect alpha beta bottom top) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_not_reachableSource_goodBoundary_transverse_atCut gamma gamma' A hAright hAleft H hHReach V alpha beta bottom top hab hbt hHstartBox hHendBox hHstartLeft hHendRight hHBox hVstartBottom hVendTop hVstartX hVendX hVBox

/--
[rlc_twoChannelFullPhysical_not_reachableSource_goodBoundary_collared_atCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_not_reachableSource_goodBoundary_collared_atCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {a b f g : Site 2}
  {H : (hypercubicLattice 2).Walk a b}
  {V : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk f g}
  {alpha beta bottom top : Int}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hHReach : ∀ v ∈ H.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hab : alpha < beta)
  (hbt : bottom ≤ top)
  (hHBox : ∀ z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support, z ∈ rect alpha beta bottom top)
  (hVBox : ∀ z ∈ (StatMech.TwoDim.zfe_faceSubdiv ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))).support, z ∈ rect alpha beta bottom top)
  (hLower : ∀ z ∈ (Lattice.horizontalWallExtension alpha beta (StatMech.TwoDim.zfe_primalSubdiv H)).support, z ∈ (sw_vertSeg (StatMech.TwoDim.zfe_faceEmb f 0) bottom (StatMech.TwoDim.zfe_faceEmb f 1)).support → z ∈ (StatMech.TwoDim.zfe_faceSubdiv ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))).support)
  (hUpper : ∀ z ∈ (Lattice.horizontalWallExtension alpha beta (StatMech.TwoDim.zfe_primalSubdiv H)).support, z ∈ (sw_vertSeg (StatMech.TwoDim.zfe_faceEmb g 0) (StatMech.TwoDim.zfe_faceEmb g 1) top).support → z ∈ (StatMech.TwoDim.zfe_faceSubdiv ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))).support)
  (hLeft : ∀ z ∈ (StatMech.TwoDim.zfe_faceSubdiv ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))).support, z ∈ (sw_horizSeg (StatMech.TwoDim.zfe_primalEmb a 1) alpha (StatMech.TwoDim.zfe_primalEmb a 0)).support → z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support)
  (hRight : ∀ z ∈ (StatMech.TwoDim.zfe_faceSubdiv ((V.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))).support, z ∈ (sw_horizSeg (StatMech.TwoDim.zfe_primalEmb b 1) (StatMech.TwoDim.zfe_primalEmb b 0) beta).support → z ∈ (StatMech.TwoDim.zfe_primalSubdiv H).support) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_not_reachableSource_goodBoundary_collared_atCut gamma gamma' A hAright hAleft H hHReach V alpha beta bottom top hab hbt hHBox hVBox hLower hUpper hLeft hRight

/--
[rlc_twoChannelFullPhysical_goodBoundary_reachable_staticCutTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodBoundary_reachable_staticCutTarget_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {f g : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hfg : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Reachable f g) :
-- imply
  (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable (rlc_twoChannelFullPhysicalLiftFace gamma f) (rlc_twoChannelFullPhysicalLiftFace gamma g) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodBoundary_reachable_staticCutTarget gamma gamma' A hAright hAleft hfg

/--
[rlc_twoChannelFullPhysical_staticCutTargetConnector_of_goodComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_staticCutTargetConnector_of_goodComponent_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hgood : RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) :
-- imply
  ∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_staticCutTargetConnector_of_goodComponent gamma gamma' A hAright hAleft hgood

/--
[rlc_twoChannelFullPhysical_staticCutFailure_separates_traceComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_staticCutFailure_separates_traceComponents_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {x y a b : RlcConnectorVertex n}
-- given
  (hfailure : ¬∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable x y)
  (hx : rlc_connectorOnRight gamma x)
  (hy : rlc_connectorOnLeft gamma' y)
  (hxa : (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable x a)
  (hyb : (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable y b) :
-- imply
  ¬(rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable a b := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_staticCutFailure_separates_traceComponents gamma gamma' A hfailure hx hy hxa hyb

/--
[RlcBookFaithfulTracePair.scale_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma scale_pos_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  0 < n := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.scale_pos hfaith

/--
[RlcBookFaithfulTracePair.origin_mem_connectorAllowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma origin_mem_connectorAllowed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  origin 2 ∈ rlc_connectorAllowed gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.origin_mem_connectorAllowed hfaith

/--
[RlcBookFaithfulTracePair.origin_mem_connectorOriginRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma origin_mem_connectorOriginRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  origin 2 ∈ rlc_connectorOriginRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.origin_mem_connectorOriginRegion hfaith

/--
[RlcBookFaithfulTracePair.axisGap_mem_connectorOriginRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma axisGap_mem_connectorOriginRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 < t)
  (habove : t < (gamma'.1.2.1 : Site 2) 1) :
-- imply
  (![0, t] : Site 2) ∈ rlc_connectorOriginRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.axisGap_mem_connectorOriginRegion hfaith t hbelow habove

/--
[rlc_bookFaithful_axisGapVertical_mem_connectorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_axisGapVertical_mem_connectorEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 < t)
  (habove : t + 1 < (gamma'.1.2.1 : Site 2) 1) :
-- imply
  s((![0, t] : Site 2), ![0, t + 1]) ∈ rlc_connectorEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_axisGapVertical_mem_connectorEdges hfaith t hbelow habove

/--
[rlc_bookFaithful_axisGapVertical_preimage_mem_connectorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_axisGapVertical_preimage_mem_connectorEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 < t)
  (habove : t < (gamma'.1.2.1 : Site 2) 1) :
-- imply
  rlc_pimsEdgeEquiv s((![0, t] : Site 2), ![0, t + 1]) ∈ rlc_connectorEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_axisGapVertical_preimage_mem_connectorEdges hfaith t hbelow habove

/--
[rlc_bookFaithful_axisIntervalVertical_mem_connectorEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_axisIntervalVertical_mem_connectorEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
  (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  s((![0, t] : Site 2), ![0, t + 1]) ∈ rlc_connectorEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_axisIntervalVertical_mem_connectorEdges hfaith t hbelow habove

/--
[rlc_bookFaithful_axisInterval_cutCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_axisInterval_cutCrossing_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (Site 2)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ z ∈ rlc_pathVertices gamma.1, z ∈ A)
  (hAleft : ∀ z ∈ rlc_pathVertices gamma'.1, z ∉ A) :
-- imply
  ∃ t : Int, (gamma.1.1 : Site 2) 1 ≤ t ∧ t + 1 ≤ (gamma'.1.2.1 : Site 2) 1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut A s((![0, t] : Site 2), ![0, t + 1]) ∧ s((![0, t] : Site 2), ![0, t + 1]) ∈ rlc_connectorEdges gamma gamma' ∧ (t = (gamma.1.1 : Site 2) 1 ∨ rlc_pimsEdgeEquiv s((![0, t] : Site 2), ![0, t + 1]) ∈ rlc_connectorEdges gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_axisInterval_cutCrossing hfaith A hAright hAleft

/--
[rlc_bookFaithful_lowerAxis_preimage_mem_reflectedRightPathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_lowerAxis_preimage_mem_reflectedRightPathEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  rlc_pimsEdgeEquiv s((![0, (gamma.1.1 : Site 2) 1] : Site 2), ![0, (gamma.1.1 : Site 2) 1 + 1]) ∈ rlc_reflectedPathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_lowerAxis_preimage_mem_reflectedRightPathEdges hfaith

/--
[rlc_bookFaithful_upperAxis_horizontal_mem_reflectedLeftPathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_upperAxis_horizontal_mem_reflectedLeftPathEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  s((![0, (gamma'.1.2.1 : Site 2) 1] : Site 2), ![1, (gamma'.1.2.1 : Site 2) 1]) ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_upperAxis_horizontal_mem_reflectedLeftPathEdges hfaith

/--
[rlc_bookFaithful_upperAxis_horizontal_mem_originalLeftPathEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_upperAxis_horizontal_mem_originalLeftPathEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  s((![-1, (gamma'.1.2.1 : Site 2) 1] : Site 2), ![0, (gamma'.1.2.1 : Site 2) 1]) ∈ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_upperAxis_horizontal_mem_originalLeftPathEdges hfaith

/--
[rlc_bookFaithful_upperAxis_horizontal_twoChannelWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_upperAxis_horizontal_twoChannelWitness_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s((![0, (gamma'.1.2.1 : Site 2) 1] : Site 2), ![1, (gamma'.1.2.1 : Site 2) 1]) := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_upperAxis_horizontal_twoChannelWitness hfaith

/--
[rlc_bookFaithful_upperAxis_columnSource_twoChannel_or_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_upperAxis_columnSource_twoChannel_or_original_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s((![-1, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2), ![-1, (gamma'.1.2.1 : Site 2) 1])) ∨ s((![-1, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2), ![-1, (gamma'.1.2.1 : Site 2) 1]) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_upperAxis_columnSource_twoChannel_or_original hfaith

/--
[rlc_bookFaithful_upperAxis_fullPhysical_or_original](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_upperAxis_fullPhysical_or_original_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  (∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', target.1.1.map Subtype.val = s((![0, (gamma'.1.2.1 : Site 2) 1] : Site 2), ![1, (gamma'.1.2.1 : Site 2) 1]) ∧ (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val = s((![-1, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2), ![-1, (gamma'.1.2.1 : Site 2) 1])) ∨ s((![-1, (gamma'.1.2.1 : Site 2) 1 - 1] : Site 2), ![-1, (gamma'.1.2.1 : Site 2) 1]) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_upperAxis_fullPhysical_or_original hfaith

/--
[RlcBookFaithfulTracePair.axisFaceBand_mem_centralFaceRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma axisFaceBand_mem_centralFaceRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {k : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 ≤ k)
  (habove : k < (gamma'.1.2.1 : Site 2) 1) :
-- imply
  (![0, k] : Site 2) ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.axisFaceBand_mem_centralFaceRegion hfaith k hbelow habove

/--
[rlc_bookFaithful_axisIntervalVertical_not_mem_originalTraceEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_axisIntervalVertical_not_mem_originalTraceEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
  (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  s((![0, t] : Site 2), ![0, t + 1]) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_axisIntervalVertical_not_mem_originalTraceEdges hfaith t hbelow habove

/--
[rlc_bookFaithful_axisIntervalPreimage_not_mem_originalTraceEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_axisIntervalPreimage_not_mem_originalTraceEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
  (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  s((![-1, t] : Site 2), ![0, t]) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_axisIntervalPreimage_not_mem_originalTraceEdges hfaith t hbelow habove

/--
[rlc_bookFaithful_axisIntervalVertical_twoChannelWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_axisIntervalVertical_twoChannelWitness_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
  (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s((![0, t] : Site 2), ![0, t + 1]) := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_axisIntervalVertical_twoChannelWitness hfaith t hbelow habove

/--
[rlc_bookFaithful_axisIntervalPreimage_twoChannelWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_axisIntervalPreimage_twoChannelWitness_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
  (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s((![-1, t] : Site 2), ![0, t]) := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_axisIntervalPreimage_twoChannelWitness hfaith t hbelow habove

/--
[rlc_bookFaithful_axisInterval_fullPhysicalTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_axisInterval_fullPhysicalTarget_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t : Int}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hbelow : (gamma.1.1 : Site 2) 1 ≤ t)
  (habove : t + 1 ≤ (gamma'.1.2.1 : Site 2) 1) :
-- imply
  ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', target.1.1.map Subtype.val = s((![0, t] : Site 2), ![0, t + 1]) := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_axisInterval_fullPhysicalTarget hfaith t hbelow habove

/--
[rlc_twoChannelFullPhysical_goodBoundary_of_source_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodBoundary_of_source_bdEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
  {p q : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q)
  (hsource : (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val = s(p, q))
  (hbd : bdEdge (rlc_twoChannelFullFilledReachSet gamma gamma' omega) s(p, q)) :
-- imply
  ∃ f g : Site 2, (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj f g ∧ sharedPrimalEdge f g = s(p, q) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodBoundary_of_source_bdEdge omega target hpq hsource hbd

/--
[rlc_bookFaithful_fullFilledAxisExit_carrier_or_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_fullFilledAxisExit_carrier_or_top_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ∃ (t : Int) (f g : Site 2), (gamma.1.1 : Site 2) 1 ≤ t ∧ t + 1 ≤ (gamma'.1.2.1 : Site 2) 1 ∧ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g ∧ sharedPrimalEdge f g = s((![0, t] : Site 2), ![0, t + 1]) ∧ (RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g ∨ t + 1 = (gamma'.1.2.1 : Site 2) 1) := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_fullFilledAxisExit_carrier_or_top hfaith omega hno

/--
[rlc_bookFaithful_fullFilledBoundary_physicalAxisAnchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_fullFilledBoundary_physicalAxisAnchor_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ∃ f g : Site 2, (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj f g := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_fullFilledBoundary_physicalAxisAnchor hfaith omega hno

/--
[rlc_bookFaithful_fullFilledBoundary_axisAnchorPaths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_fullFilledBoundary_axisAnchorPaths_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ∃ (f g x y : Site 2), (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj f g ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ Nonempty ((faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk f x) ∧ Nonempty ((faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk f y) := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_fullFilledBoundary_axisAnchorPaths hfaith omega hno

/--
[rlc_bookFaithful_goodComponent_or_axisAnchorFirstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_goodComponent_or_axisAnchorFirstExit_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨ ∃ (f g z u v : Site 2) (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk f u) (r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v z), (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj f g ∧ (rlc_dualReflect z ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect z ∈ rlc_pathVertices gamma'.1) ∧ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u v := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_goodComponent_or_axisAnchorFirstExit hfaith omega hno

/--
[rlc_bookFaithful_staticCut_goodBoundaryAxisEdge_or_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_staticCut_goodBoundaryAxisEdge_or_top_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
-- imply
  ∃ (t : Int) (f g : Site 2), (gamma.1.1 : Site 2) 1 ≤ t ∧ t + 1 ≤ (gamma'.1.2.1 : Site 2) 1 ∧ sharedPrimalEdge f g = s((![0, t] : Site 2), ![0, t + 1]) ∧ ((rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Adj f g ∨ t + 1 = (gamma'.1.2.1 : Site 2) 1) := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_staticCut_goodBoundaryAxisEdge_or_top hfaith A hAright hAleft

/--
[rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff_eq
  {n : Int}
  {A : Set (RlcConnectorVertex n)}
  {e : Sym2 (RlcConnectorVertex n)} :
-- imply
  rlc_twoChannelFullPhysicalEdgeCrossesCut A e ↔ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut A) (e.map Subtype.val) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalEdgeCrossesCut_liftVertexCut_iff A e

/--
[rlc_twoChannelFullPhysical_goodBoundary_B_monochromatic_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodBoundary_B_monochromatic_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {f g : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hfg : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Adj f g) :
-- imply
  (rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔ rlc_dualReflect g ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodBoundary_B_monochromatic_of_noPair gamma gamma' A B hAright hAleft hnoPair hfg

/--
[rlc_twoChannelFullPhysical_goodWalk_B_monochromatic_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodWalk_B_monochromatic_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {f g : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk f g}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1) :
-- imply
  (rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔ rlc_dualReflect g ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodWalk_B_monochromatic_of_noPair gamma gamma' A B hAright hAleft hnoPair q

/--
[rlc_twoChannelFullPhysical_noGoodComponent_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noGoodComponent_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1) :
-- imply
  ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noGoodComponent_of_noPair gamma gamma' A B hAright hAleft hBright hBleft hnoPair

/--
[rlc_twoChannelFullPhysical_goodPrefixEndpoints_B_separated_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodPrefixEndpoints_B_separated_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  rlc_dualReflect ur ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ∧ rlc_dualReflect ul ∉ rlc_twoChannelFullPhysicalLiftVertexCut B := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodPrefixEndpoints_B_separated_of_noPair gamma gamma' A B hAright hAleft hBright hBleft hnoPair hxPath hyPath qr ql

/--
[rlc_twoChannelFullPhysical_contactCycle_BChanging_noncarrier_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_BChanging_noncarrier_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ c.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_BChanging_noncarrier_of_noPair gamma gamma' A B hAright hAleft hBright hBleft hnoPair c hx hy hxPath hyPath

/--
[rlc_twoChannelFullPhysical_BChanging_terminalClassification_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_BChanging_terminalClassification_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {f g : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj f g)
  (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g)) :
-- imply
  ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ∨ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧ ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_BChanging_terminalClassification_of_noPair gamma gamma' A B hAright hAleft hnoPair hfg hcrossB

/--
[rlc_twoChannelFullPhysical_staticCutTargetFailure_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_staticCutTargetFailure_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
-- given
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1) :
-- imply
  ¬∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_staticCutTargetFailure_of_noPair gamma gamma' A B hBright hBleft hnoPair

/--
[rlc_bookFaithful_noPair_axisAnchorFirstNoncarrier_to_oppositeB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_noPair_axisAnchorFirstNoncarrier_to_oppositeB_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1) :
-- imply
  ∃ (f g z u v : Site 2) (w : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk f z) (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk f u) (r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk v z) (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj u v), (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Adj f g ∧ (rlc_dualReflect z ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect z ∈ rlc_pathVertices gamma'.1) ∧ ¬(rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔ rlc_dualReflect z ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) ∧ (rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔ rlc_dualReflect u ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) ∧ ¬(rlc_dualReflect u ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ↔ rlc_dualReflect z ∈ rlc_twoChannelFullPhysicalLiftVertexCut B) ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u v ∧ w = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).append (.cons huv r) ∧ s(u, v) ∈ w.edges ∧ r.length < w.length := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_noPair_axisAnchorFirstNoncarrier_to_oppositeB hfaith A B hAright hAleft hBright hBleft hnoPair

/--
[rlc_bookFaithful_staticCut_axisFullPhysicalPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_staticCut_axisFullPhysicalPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
-- imply
  ∃ (t : Int) (target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'), (gamma.1.1 : Site 2) 1 ≤ t ∧ t + 1 ≤ (gamma'.1.2.1 : Site 2) 1 ∧ target.1.1.map Subtype.val = s((![0, t] : Site 2), ![0, t + 1]) ∧ (rlc_twoChannelFullPhysicalSourceEdge target).1.map Subtype.val = s((![-1, t] : Site 2), ![0, t]) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut A target.1.1 := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_staticCut_axisFullPhysicalPair hfaith A hAright hAleft

/--
[rlc_bookFaithful_staticCut_axisFullPhysicalTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFaithful_staticCut_axisFullPhysicalTarget_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
-- imply
  ∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A target.1.1 := by
-- proof
  apply StatMech.Universality.rlc_bookFaithful_staticCut_axisFullPhysicalTarget hfaith A hAright hAleft

/--
[RlcBookFaithfulTracePair.doubledAxisContact_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma doubledAxisContact_geometry_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  let f := rlc_dualReflect.symm (gamma.1.1 : Site 2) let g := rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) StatMech.TwoDim.zfe_faceEmb f 0 = -1 ∧ StatMech.TwoDim.zfe_faceEmb g 0 = -1 ∧ StatMech.TwoDim.zfe_faceEmb f 1 < StatMech.TwoDim.zfe_faceEmb g 1 := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.doubledAxisContact_geometry hfaith

/--
[RlcBookFaithfulTracePair.dualFace_rightContact_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma dualFace_rightContact_position_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hf : rlc_dualReflect f ∈ rlc_pathVertices gamma.1) :
-- imply
  (f 0 = -1 ∧ f 1 < -1) ∨ f 0 < -1 := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.dualFace_rightContact_position hfaith hf

/--
[RlcBookFaithfulTracePair.dualFace_rightContact_axisColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma dualFace_rightContact_axisColumn_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hf : rlc_dualReflect f ∈ rlc_pathVertices gamma.1)
  (hf0 : f 0 = -1) :
-- imply
  f 1 < -1 := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.dualFace_rightContact_axisColumn hfaith hf hf0

/--
[RlcBookFaithfulTracePair.dualFace_leftContact_position](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma dualFace_leftContact_position_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hf : rlc_dualReflect f ∈ rlc_pathVertices gamma'.1) :
-- imply
  (f 0 = -1 ∧ 0 ≤ f 1) ∨ 0 ≤ f 0 := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.dualFace_leftContact_position hfaith hf

/--
[RlcBookFaithfulTracePair.dualFace_leftContact_axisColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma dualFace_leftContact_axisColumn_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hf : rlc_dualReflect f ∈ rlc_pathVertices gamma'.1)
  (hf0 : f 0 = -1) :
-- imply
  0 ≤ f 1 := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.dualFace_leftContact_axisColumn hfaith hf hf0

/--
[rlc_twoChannelFullPhysicalTargetCarrierGeometry_centralCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalTargetCarrierGeometry_centralCarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph S).Adj f g)
  (htarget : RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalTargetCarrierGeometry_centralCarrier gamma gamma' hfg htarget

/--
[rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginal_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph S).Adj f g)
  (hfRight : rlc_dualReflect f ∉ rlc_pathVertices gamma.1)
  (hfLeft : rlc_dualReflect f ∉ rlc_pathVertices gamma'.1)
  (hcentral : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g) :
-- imply
  RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginal gamma gamma' hfg hfRight hfLeft hcentral

/--
[rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginalEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph S).Adj f g)
  (hnotOriginal : s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
  (hcentral : RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' f g) :
-- imply
  RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_centralCarrier_nonoriginalEdge gamma gamma' hfg hnotOriginal hcentral

/--
[rlc_twoChannelFullPhysical_nonopposite_targetContinuation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_nonopposite_targetContinuation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {a u v : Site 2}
-- given
  (hau : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj a u)
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hav : a ≠ v)
  (huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1)
  (huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1)
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n)
  (hnotWall : s(rlc_dualReflect a, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hnonopposite : ¬((rlc_dualReflect a) 0 + (rlc_dualReflect v) 0 = 2 * (rlc_dualReflect u) 0 ∧ (rlc_dualReflect a) 1 + (rlc_dualReflect v) 1 = 2 * (rlc_dualReflect u) 1)) :
-- imply
  RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_nonopposite_targetContinuation hau huv hav huRight huLeft huInterior hnotWall hnonopposite

/--
[rlc_twoChannelFullPhysical_exclusiveReflected_targetBad_allWall_or_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_exclusiveReflected_targetBad_allWall_or_opposite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hbad : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v)
  (huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1)
  (huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1)
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n) :
-- imply
  (∀ a : Site 2, (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj a u → a ≠ v → s(rlc_dualReflect a, rlc_dualReflect u) ∈ rlc_connectorFourTraceEdges gamma gamma') ∨ ∃ a : Site 2, (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj a u ∧ a ≠ v ∧ s(rlc_dualReflect a, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ ((rlc_dualReflect a) 0 + (rlc_dualReflect v) 0 = 2 * (rlc_dualReflect u) 0 ∧ (rlc_dualReflect a) 1 + (rlc_dualReflect v) 1 = 2 * (rlc_dualReflect u) 1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_exclusiveReflected_targetBad_allWall_or_opposite huv hbad huRight huLeft huInterior

/--
[rlc_twoChannelFullPhysical_goodWalk_end_dualReflect_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodWalk_end_dualReflect_mem_box_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x y}
-- given
  (hxBox : rlc_dualReflect x ∈ rlc_connectorBox n) :
-- imply
  rlc_dualReflect y ∈ rlc_connectorBox n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodWalk_end_dualReflect_mem_box q hxBox

/--
[rlc_twoChannelFullPhysical_targetBad_near_mem_barrier_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_targetBad_near_mem_barrier_of_interior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u v : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hxBarrier : rlc_dualReflect x ∈ rlc_connectorBarrier gamma gamma')
  (hxBox : rlc_dualReflect x ∈ rlc_connectorBox n)
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hbadTarget : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v)
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n) :
-- imply
  rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_targetBad_near_mem_barrier_of_interior hxBarrier hxBox q huv hbadTarget huInterior

/--
[rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u v : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hxBarrier : rlc_dualReflect x ∈ rlc_connectorBarrier gamma gamma')
  (hxBox : rlc_dualReflect x ∈ rlc_connectorBox n)
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hbadTarget : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) :
-- imply
  rlc_dualReflect u ∈ rlc_connectorBarrier gamma gamma' ∨ (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_targetBad_near_barrier_or_boxBoundary hxBarrier hxBox q huv hbadTarget

/--
[rlc_twoChannelFull_reflectedLeft_hit_sourceNE_not_filled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFull_reflectedLeft_hit_sourceNE_not_filled_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u w : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hw : w ∈ rlc_pathVertices gamma'.1)
  (hu : rlc_dualReflect u = rlc_flipX w) :
-- imply
  (![u 0 + 1, u 1 + 1] : Site 2) ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFull_reflectedLeft_hit_sourceNE_not_filled gamma gamma' hfaith omega hno hw hu

/--
[rlc_twoChannelFull_reflectedRight_hit_sourceNE_mem_filled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFull_reflectedRight_hit_sourceNE_mem_filled_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u w : Site 2}
-- given
  (hw : w ∈ rlc_pathVertices gamma.1)
  (hu : rlc_dualReflect u = rlc_flipX w) :
-- imply
  (![u 0 + 1, u 1 + 1] : Site 2) ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFull_reflectedRight_hit_sourceNE_mem_filled gamma gamma' omega hw hu

/--
[rlc_twoChannelFullFilledBoundary_preimage_not_exposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullFilledBoundary_preimage_not_exposed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
-- imply
  sharedPrimalEdge f g ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullFilledBoundary_preimage_not_exposed gamma gamma' omega hfg

/--
[rlc_twoChannelFull_reflectedHit_boundary_step_ne_right_of_south_exposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFull_reflectedHit_boundary_step_ne_right_of_south_exposed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v w : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hu : rlc_dualReflect u = rlc_flipX w)
  (hsouth : s((![w 0, w 1 - 1] : Site 2), w) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  v ≠ ![u 0 + 1, u 1] := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFull_reflectedHit_boundary_step_ne_right_of_south_exposed gamma gamma' omega huv hu hsouth

/--
[rlc_twoChannelFull_reflectedHit_boundary_step_ne_top_of_west_exposed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFull_reflectedHit_boundary_step_ne_top_of_west_exposed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v w : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hu : rlc_dualReflect u = rlc_flipX w)
  (hwest : s((![w 0 - 1, w 1] : Site 2), w) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  v ≠ ![u 0, u 1 + 1] := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFull_reflectedHit_boundary_step_ne_top_of_west_exposed gamma gamma' omega huv hu hwest

/--
[rlc_twoChannelFull_reflectedLeft_opposite_continuation_centralCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFull_reflectedLeft_opposite_continuation_centralCarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v b w h : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma'.1)
  (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
  (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
  (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect v = rlc_flipX r)
  (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 = 2 * (rlc_dualReflect v) 0 ∧ (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 = 2 * (rlc_dualReflect v) 1)
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFull_reflectedLeft_opposite_continuation_centralCarrier gamma gamma' omega huv hvb hub hvflip hw hvRight hvLeft hvFlipRight hopp hvInterior hnotIn hhRegion hh

/--
[rlc_twoChannelFull_reflectedLeft_opposite_continuation_targetCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFull_reflectedLeft_opposite_continuation_targetCarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v b w h : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma'.1)
  (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
  (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
  (hvFlipRight : ¬ ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect v = rlc_flipX r)
  (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 = 2 * (rlc_dualReflect v) 0 ∧ (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 = 2 * (rlc_dualReflect v) 1)
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFull_reflectedLeft_opposite_continuation_targetCarrier gamma gamma' omega huv hvb hub hvflip hw hvRight hvLeft hvFlipRight hopp hvInterior hnotIn hhRegion hh

/--
[rlc_twoChannelFull_reflectedRight_opposite_continuation_centralCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFull_reflectedRight_opposite_continuation_centralCarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v b w h : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma.1)
  (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
  (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
  (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1, rlc_dualReflect v = rlc_flipX r)
  (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 = 2 * (rlc_dualReflect v) 0 ∧ (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 = 2 * (rlc_dualReflect v) 1)
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcCentralFaceReflectedEdgeCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFull_reflectedRight_opposite_continuation_centralCarrier gamma gamma' omega huv hvb hub hvflip hw hvRight hvLeft hvFlipLeft hopp hvInterior hnotIn hhRegion hh

/--
[rlc_twoChannelFull_reflectedRight_opposite_continuation_targetCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFull_reflectedRight_opposite_continuation_targetCarrier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v b w h : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hvb : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj v b)
  (hub : u ≠ b)
  (hvflip : rlc_dualReflect v = rlc_flipX w)
  (hw : w ∈ rlc_pathVertices gamma.1)
  (hvRight : rlc_dualReflect v ∉ rlc_pathVertices gamma.1)
  (hvLeft : rlc_dualReflect v ∉ rlc_pathVertices gamma'.1)
  (hvFlipLeft : ¬ ∃ r ∈ rlc_pathVertices gamma'.1, rlc_dualReflect v = rlc_flipX r)
  (hopp : (rlc_dualReflect u) 0 + (rlc_dualReflect b) 0 = 2 * (rlc_dualReflect v) 0 ∧ (rlc_dualReflect u) 1 + (rlc_dualReflect b) 1 = 2 * (rlc_dualReflect v) 1)
  (hvInterior : -2 * n < (rlc_dualReflect v) 0 ∧ (rlc_dualReflect v) 0 < 2 * n ∧ -n < (rlc_dualReflect v) 1 ∧ (rlc_dualReflect v) 1 < n)
  (hnotIn : s(rlc_dualReflect v, rlc_dualReflect u) ∉ rlc_connectorFourTraceEdges gamma gamma')
  (hhRegion : h ∈ rlc_connectorCentralFaceRegion gamma gamma')
  (hh : h ∈ flankFaces (rlc_dualReflect v) (rlc_dualReflect u)) :
-- imply
  RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' v b := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFull_reflectedRight_opposite_continuation_targetCarrier gamma gamma' omega huv hvb hub hvflip hw hvRight hvLeft hvFlipLeft hopp hvInterior hnotIn hhRegion hh

/--
[rlc_twoChannelFullPhysical_interior_exclusiveReflected_targetBad_allWall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_interior_exclusiveReflected_targetBad_allWall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hbad : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v)
  (huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1)
  (huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1)
  (huReflected : (0 < (rlc_dualReflect u) 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1, rlc_dualReflect u = rlc_flipX w) ∨ ((rlc_dualReflect u) 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1, rlc_dualReflect u = rlc_flipX w))
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n) :
-- imply
  ∀ a : Site 2, (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj a u → a ≠ v → s(rlc_dualReflect a, rlc_dualReflect u) ∈ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_interior_exclusiveReflected_targetBad_allWall huv hbad huRight huLeft huReflected huInterior

/--
[rlc_twoChannelFullPhysical_targetBad_prefix_allWall_or_terminalWallRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_targetBad_prefix_allWall_or_terminalWallRun_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u v : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hbad : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v)
  (huRight : rlc_dualReflect u ∉ rlc_pathVertices gamma.1)
  (huLeft : rlc_dualReflect u ∉ rlc_pathVertices gamma'.1)
  (huReflected : (0 < (rlc_dualReflect u) 0 ∧ ∃ w ∈ rlc_pathVertices gamma'.1, rlc_dualReflect u = rlc_flipX w) ∨ ((rlc_dualReflect u) 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1, rlc_dualReflect u = rlc_flipX w))
  (huInterior : -2 * n < (rlc_dualReflect u) 0 ∧ (rlc_dualReflect u) 0 < 2 * n ∧ -n < (rlc_dualReflect u) 1 ∧ (rlc_dualReflect u) 1 < n) :
-- imply
  (∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma') ∨ RlcTwoChannelFullPhysicalTerminalWallRunAt gamma gamma' omega q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_targetBad_prefix_allWall_or_terminalWallRun q huv hbad huRight huLeft huReflected huInterior

/--
[RlcBookFaithfulTracePair.reflectedTraceVertices_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma reflectedTraceVertices_disjoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : ∃ r ∈ rlc_pathVertices gamma.1, z = rlc_flipX r)
  (hzLeft : ∃ l ∈ rlc_pathVertices gamma'.1, z = rlc_flipX l) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.reflectedTraceVertices_disjoint hfaith hzRight hzLeft

/--
[RlcBookFaithfulTracePair.traceVertices_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma traceVertices_disjoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : z ∈ rlc_pathVertices gamma'.1) :
-- imply
  False := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.traceVertices_disjoint hfaith hzRight hzLeft

/--
[rlc_twoChannelFullPhysical_goodWallTarget_reflected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodWallTarget_reflected_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hfg : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj f g)
  (hwall : s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_connectorFourTraceEdges gamma gamma') :
-- imply
  s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma.1 ∨ s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodWallTarget_reflected hfg hwall

/--
[rlc_twoChannelFullPhysical_goodWallWalk_oneReflectedFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodWallWalk_oneReflectedFamily_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x y}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hall : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma') :
-- imply
  q.Nil ∨ (∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∨ (∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodWallWalk_oneReflectedFamily hfaith q hall

/--
[rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x y}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnotNil : ¬q.Nil)
  (hall : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hyLeft : ∃ l ∈ rlc_pathVertices gamma'.1, rlc_dualReflect y = rlc_flipX l) :
-- imply
  ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodWallWalk_reflectedLeft_of_terminal hfaith q hnotNil hall hyLeft

/--
[rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x y}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnotNil : ¬q.Nil)
  (hall : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hyRight : ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect y = rlc_flipX r) :
-- imply
  ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodWallWalk_reflectedRight_of_terminal hfaith q hnotNil hall hyRight

/--
[rlc_twoChannelFullPhysical_reflectedLeftWalk_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftWalk_start_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x y}
-- given
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (hy : ∃ l ∈ rlc_pathVertices gamma'.1, rlc_dualReflect y = rlc_flipX l) :
-- imply
  ∃ l ∈ rlc_pathVertices gamma'.1, rlc_dualReflect x = rlc_flipX l := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftWalk_start q hedges hy

/--
[rlc_twoChannelFullPhysical_reflectedRightWalk_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedRightWalk_start_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x y}
-- given
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (hy : ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect y = rlc_flipX r) :
-- imply
  ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect x = rlc_flipX r := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedRightWalk_start q hedges hy

/--
[rlc_twoChannelFullPhysical_orderedRightContact_reflectedLeft_start_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_orderedRightContact_reflectedLeft_start_eq_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x y}
-- given
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hfirst : ∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (hy : ∃ l ∈ rlc_pathVertices gamma'.1, rlc_dualReflect y = rlc_flipX l) :
-- imply
  rlc_dualReflect x = z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_orderedRightContact_reflectedLeft_start_eq right q hxOrder hfirst hedges hy

/--
[rlc_twoChannelFullPhysical_rightContact_reflectedRight_start_eq_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rightContact_reflectedRight_start_eq_axis_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x y}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (hy : ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect y = rlc_flipX r) :
-- imply
  rlc_dualReflect x = (gamma.1.1 : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rightContact_reflectedRight_start_eq_axis hfaith q hxPath hedges hy

/--
[rlc_twoChannelFullPhysical_leftContact_reflectedLeft_start_eq_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_leftContact_reflectedLeft_start_eq_axis_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x y}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma'.1)
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (hy : ∃ l ∈ rlc_pathVertices gamma'.1, rlc_dualReflect y = rlc_flipX l) :
-- imply
  rlc_dualReflect x = (gamma'.1.2.1 : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_leftContact_reflectedLeft_start_eq_axis hfaith q hxPath hedges hy

/--
[rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_suffix_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_suffix_at_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
  {c u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk c u}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hcEnd : rlc_dualReflect c = (gamma'.1.2.1 : Site 2))
  (hqReflectedLeft : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) :
-- imply
  ∃ (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support), rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_suffix_at hnoGood z hzRight hzLeft q hcEnd hqReflectedLeft

/--
[rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_suffix_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_suffix_at_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
  {c u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk c u}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hcStart : rlc_dualReflect c = (gamma.1.1 : Site 2))
  (hqReflectedRight : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) :
-- imply
  ∃ (hz : rlc_flipX z ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support), rlc_dualReflect u ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hz).support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_suffix_at hnoGood z hzRight hzLeft q hcStart hqReflectedRight

/--
[rlc_twoChannelFullPhysical_leftContact_terminalReflectedLeft_sameSide_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_leftContact_terminalReflectedLeft_sameSide_at_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
  {x u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxLeft : rlc_dualReflect x ∈ rlc_pathVertices gamma'.1)
  (hrun : RlcTwoChannelFullPhysicalTerminalWallRunAt gamma gamma' omega q)
  (huLeft : ∃ l ∈ rlc_pathVertices gamma'.1, rlc_dualReflect u = rlc_flipX l) :
-- imply
  ∃ (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support) (b : Site 2), rlc_dualReflect b ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support ∧ rlc_dualReflect u ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support ∧ (rlc_dualReflect b ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support ↔ rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_leftContact_terminalReflectedLeft_sameSide_at hfaith hnoGood z hzRight hzLeft q hxLeft hrun huLeft

/--
[rlc_twoChannelFullPhysical_rightContact_terminalReflectedRight_sameSide_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rightContact_terminalReflectedRight_sameSide_at_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
  {x u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxRight : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hrun : RlcTwoChannelFullPhysicalTerminalWallRunAt gamma gamma' omega q)
  (huRight : ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect u = rlc_flipX r) :
-- imply
  ∃ (hz : rlc_flipX z ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support) (b : Site 2), rlc_dualReflect b ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support ∧ rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support ∧ (rlc_dualReflect b ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hz).support ↔ rlc_dualReflect u ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hz).support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rightContact_terminalReflectedRight_sameSide_at hfaith hnoGood z hzRight hzLeft q hxRight hrun huRight

/--
[rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {c u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk c u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hcEnd : rlc_dualReflect c = (gamma'.1.2.1 : Site 2))
  (hqReflectedLeft : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) :
-- imply
  ∃ (z : Site 2) (hz : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect u ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hz).support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftAxisWalk_end_mem_firstIntersectionSuffix hfaith hnoGood q hcEnd hqReflectedLeft

/--
[rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {c u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk c u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hcStart : rlc_dualReflect c = (gamma.1.1 : Site 2))
  (hqReflectedRight : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) :
-- imply
  ∃ (z : Site 2) (hz : rlc_flipX z ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect u ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hz).support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedRightAxisWalk_end_mem_firstIntersectionSuffix hfaith hnoGood q hcStart hqReflectedRight

/--
[rlc_twoChannelFullPhysical_sourceCarrier_of_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceCarrier_of_planar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hplanar : sharedPrimalEdge f g ∈ rlc_connectorCentralFacePlanarEdges gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceCarrier_of_planar gamma gamma' omega hfg hplanar

/--
[rlc_twoChannelFullPhysical_sourceCarrier_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceCarrier_planar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g : Site 2}
-- given
  (hsource : RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) :
-- imply
  sharedPrimalEdge f g ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceCarrier_planar gamma gamma' hsource

/--
[rlc_twoChannelFullPhysical_sourceCarrier_iff_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceCarrier_iff_planar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g ↔ sharedPrimalEdge f g ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceCarrier_iff_planar gamma gamma' omega hfg

/--
[rlc_twoChannelFullPhysical_targetCarrier_iff_planar_of_nonoriginalEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_targetCarrier_iff_planar_of_nonoriginalEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph S).Adj f g)
  (hnotOriginal : s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g ↔ s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_targetCarrier_iff_planar_of_nonoriginalEdge gamma gamma' hfg hnotOriginal

/--
[rlc_twoChannelFullPhysical_noPair_BChanging_boundary_planar_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_BChanging_boundary_planar_obstruction_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {f g : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj f g)
  (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g)) :
-- imply
  sharedPrimalEdge f g ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨ rlc_dualReflect f ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect f ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_BChanging_boundary_planar_obstruction gamma gamma' A B hAright hAleft hnoPair hfg hcrossB

/--
[rlc_twoChannelFullPhysical_noPair_orientedBChanging_boundary_not_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_orientedBChanging_boundary_not_planar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {f g : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj f g)
  (hfB : rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B)
  (hgB : rlc_dualReflect g ∉ rlc_twoChannelFullPhysicalLiftVertexCut B) :
-- imply
  sharedPrimalEdge f g ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_orientedBChanging_boundary_not_planar gamma gamma' A B hAright hAleft hBright hBleft hnoPair hfg hfB hgB

/--
[rlc_twoChannelFullPhysical_contactCycle_BChanging_not_planar_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_BChanging_not_planar_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ c.edges ∧ rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ∧ rlc_dualReflect g ∉ rlc_twoChannelFullPhysicalLiftVertexCut B ∧ (sharedPrimalEdge f g ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorCentralFacePlanarEdges gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_BChanging_not_planar_of_noPair gamma gamma' A B hAright hAleft hBright hBleft hnoPair c hx hy hxPath hyPath

/--
[rlc_twoChannelFullPhysical_sourceBad_not_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceBad_not_planar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hbadSource : ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) :
-- imply
  sharedPrimalEdge f g ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceBad_not_planar gamma gamma' omega hfg hbadSource

/--
[rlc_twoChannelFullPhysical_reachable_interior_nonbarrier_edge_planar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachable_interior_nonbarrier_edge_planar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p q : Site 2}
-- given
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧ -n < p 1 ∧ p 1 < n)
  (hpBarrier : p ∉ rlc_connectorBarrier gamma gamma')
  (hqBox : q ∈ rlc_connectorBox n)
  (hpqAdj : (hypercubicLattice 2).Adj p q) :
-- imply
  s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachable_interior_nonbarrier_edge_planar gamma gamma' omega hpReach hpInterior hpBarrier hqBox hpqAdj

/--
[rlc_twoChannelFullPhysical_reachable_interior_edge_planar_or_last_wall_or_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachable_interior_edge_planar_or_last_wall_or_opposite_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p q : Site 2}
-- given
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧ -n < p 1 ∧ p 1 < n)
  (hqBox : q ∈ rlc_connectorBox n)
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
  (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, q) = false) :
-- imply
  s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨ ∃ z : Site 2, (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧ (s(p, z) ∈ rlc_connectorFourTraceEdges gamma gamma' ∨ (z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachable_interior_edge_planar_or_last_wall_or_opposite gamma gamma' omega hpReach hpInterior hqBox hpqAdj hpAnchor hpqClosed

/--
[rlc_twoChannelFullPhysical_exclusiveReflectedRightEdge_sourceWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_exclusiveReflectedRightEdge_sourceWitness_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p z : Site 2}
-- given
  (hpExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p)
  (hpzAdj : (hypercubicLattice 2).Adj p z)
  (hpzTrace : s(p, z) ∈ rlc_reflectedPathEdges gamma.1) :
-- imply
  ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, z) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_exclusiveReflectedRightEdge_sourceWitness gamma gamma' hpExclusive hpzAdj hpzTrace

/--
[rlc_twoChannelFullPhysical_exclusiveReflectedLeftEdge_sourceWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_exclusiveReflectedLeftEdge_sourceWitness_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p z : Site 2}
-- given
  (hpExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' p)
  (hpzAdj : (hypercubicLattice 2).Adj p z)
  (hpzTrace : s(p, z) ∈ rlc_reflectedPathEdges gamma'.1) :
-- imply
  ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, z) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_exclusiveReflectedLeftEdge_sourceWitness gamma gamma' hpExclusive hpzAdj hpzTrace

/--
[rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_exclusiveReflectedLeft_traceEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_exclusiveReflectedLeft_traceEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph S).Adj f g)
  (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f))
  (htrace : s(rlc_dualReflect f, rlc_dualReflect g) ∈ rlc_reflectedPathEdges gamma'.1) :
-- imply
  RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalTargetCarrierGeometry_of_exclusiveReflectedLeft_traceEdge gamma gamma' hfg hfExclusive htrace

/--
[rlc_twoChannelFullPhysical_targetBad_not_reflectedLeft_of_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_targetBad_not_reflectedLeft_of_exclusive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {S : Set (Site 2)}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph S).Adj f g)
  (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f))
  (hbad : ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) :
-- imply
  s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_reflectedPathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_targetBad_not_reflectedLeft_of_exclusive gamma gamma' hfg hfExclusive hbad

/--
[rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {f g : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj f g)
  (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f))
  (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g)) :
-- imply
  RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure gamma gamma' B f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_exclusiveReflectedLeft_terminalFailure gamma gamma' A B hAright hAleft hnoPair hfg hfExclusive hcross

/--
[rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_traceCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_traceCross_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p q : Site 2}
-- given
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧ -n < p 1 ∧ p 1 < n)
  (hpExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p)
  (hqBox : q ∈ rlc_connectorBox n)
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
  (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, q) = false) :
-- imply
  s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨ ∃ z : Site 2, (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧ (s(p, z) ∈ rlc_reflectedPathEdges gamma.1 ∨ (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧ ∀ y : Site 2, (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q → s(p, y) ∈ rlc_reflectedPathEdges gamma.1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_traceCross gamma gamma' omega hpReach hpInterior hpExclusive hqBox hpqAdj hpAnchor hpqClosed

/--
[rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_traceCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_traceCross_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p q : Site 2}
-- given
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧ -n < p 1 ∧ p 1 < n)
  (hpExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' p)
  (hqBox : q ∈ rlc_connectorBox n)
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
  (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, q) = false) :
-- imply
  s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨ ∃ z : Site 2, (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧ (s(p, z) ∈ rlc_reflectedPathEdges gamma'.1 ∨ (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧ ∀ y : Site 2, (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q → s(p, y) ∈ rlc_reflectedPathEdges gamma'.1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_traceCross gamma gamma' omega hpReach hpInterior hpExclusive hqBox hpqAdj hpAnchor hpqClosed

/--
[rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_sourceTraceCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_sourceTraceCross_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p q : Site 2}
-- given
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧ -n < p 1 ∧ p 1 < n)
  (hpExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p)
  (hqBox : q ∈ rlc_connectorBox n)
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
  (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, q) = false) :
-- imply
  s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨ ∃ z : Site 2, (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧ ((∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, z)) ∨ (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧ ∀ y : Site 2, (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q → ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, y))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedRight_edge_planar_or_sourceTraceCross gamma gamma' omega hpReach hpInterior hpExclusive hqBox hpqAdj hpAnchor hpqClosed

/--
[rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_sourceTraceCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_sourceTraceCross_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p q : Site 2}
-- given
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpInterior : -2 * n < p 0 ∧ p 0 < 2 * n ∧ -n < p 1 ∧ p 1 < n)
  (hpExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' p)
  (hqBox : q ∈ rlc_connectorBox n)
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpAnchor : p ≠ (rlc_connectorRightAnchor gamma : Site 2))
  (hpqClosed : rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, q) = false) :
-- imply
  s(p, q) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∨ ∃ z : Site 2, (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧ ((∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, z)) ∨ (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧ ∀ y : Site 2, (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q → ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, y))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachable_interior_exclusiveReflectedLeft_edge_planar_or_sourceTraceCross gamma gamma' omega hpReach hpInterior hpExclusive hqBox hpqAdj hpAnchor hpqClosed

/--
[rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hbad : sharedPrimalEdge f g ∉ rlc_connectorCentralFacePlanarEdges gamma gamma') :
-- imply
  ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (p ∈ rlc_connectorBarrier gamma gamma' ∨ p 0 = -2 * n ∨ p 0 = 2 * n ∨ p 1 = -n ∨ p 1 = n) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceBad_inside_barrier_or_boxBoundary gamma gamma' omega hfg hbad

/--
[rlc_twoChannelFullPhysical_sourceBad_exclusiveReflectedLeft_traceResidue_or_otherLocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceBad_exclusiveReflectedLeft_traceResidue_or_otherLocation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hsourceBad : ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) :
-- imply
  ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (p ∈ rlc_pathVertices gamma.1 ∨ (RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' p ∧ RlcTwoChannelFullPhysicalExclusiveReflectedLeftSourceTraceResidue gamma gamma' omega p q) ∨ (p 0 < 0 ∧ ∃ w ∈ rlc_pathVertices gamma.1, p = rlc_flipX w) ∨ p 0 = -2 * n ∨ p 0 = 2 * n ∨ p 1 = -n ∨ p 1 = n) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceBad_exclusiveReflectedLeft_traceResidue_or_otherLocation gamma gamma' omega hno hfg hsourceBad

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_target_or_sourceTraceResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_target_or_sourceTraceResidue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {f g : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj f g)
  (hfailure : RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure gamma gamma' B f g) :
-- imply
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_reflectedPathEdges gamma'.1) ∨ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalSourceResidue gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_target_or_sourceTraceResidue gamma gamma' A B hAright hAleft hfg hfailure

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminalSourceResidue_rightTrace_or_boxWall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminalSourceResidue_rightTrace_or_boxWall_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f))
  (hsource : RlcTwoChannelFullPhysicalReflectedLeftTerminalSourceResidue gamma gamma' omega f g) :
-- imply
  (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧ ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue gamma gamma' omega p q) ∨ p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminalSourceResidue_rightTrace_or_boxWall hn gamma gamma' omega hno hfg hfExclusive hsource

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj f g)
  (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f))
  (hfailure : RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure gamma gamma' B f g) :
-- imply
  RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminalFailure_exactResidue hn gamma gamma' A B hAright hAleft hfg hfExclusive hfailure

/--
[rlc_twoChannelFullPhysical_contactCycle_BChanging_sourceBoundary_or_targetBad_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_BChanging_sourceBoundary_or_targetBad_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ c.edges ∧ rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ∧ rlc_dualReflect g ∉ rlc_twoChannelFullPhysicalLiftVertexCut B ∧ ((∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ (p ∈ rlc_connectorBarrier gamma gamma' ∨ p 0 = -2 * n ∨ p 0 = 2 * n ∨ p 1 = -n ∨ p 1 = n) ∧ ¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∨ ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_BChanging_sourceBoundary_or_targetBad_of_noPair gamma gamma' A B hAright hAleft hBright hBleft hnoPair c hx hy hxPath hyPath

/--
[rlc_twoChannelFullPhysical_contactCycle_BChanging_exactCarrierFailure_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_BChanging_exactCarrierFailure_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ c.edges ∧ rlc_dualReflect f ∈ rlc_twoChannelFullPhysicalLiftVertexCut B ∧ rlc_dualReflect g ∉ rlc_twoChannelFullPhysicalLiftVertexCut B ∧ (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g ∨ ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_BChanging_exactCarrierFailure_of_noPair gamma gamma' A B hAright hAleft hBright hBleft hnoPair c hx hy hxPath hyPath

/--
[rlc_twoChannelFullPhysical_contactCycle_BChanging_exactNoncarrier_of_noPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_BChanging_exactNoncarrier_of_noPair_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ c.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_BChanging_exactNoncarrier_of_noPair gamma gamma' A B hAright hAleft hBright hBleft hnoPair c hx hy hxPath hyPath

/--
[rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
-- imply
  (¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∨ sharedPrimalEdge f g ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundaryBad_target_or_sourceNotPlanar gamma gamma' omega hfg hbad

/--
[rlc_twoChannelFullPhysical_boundary_insideSourceWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_insideSourceWitness_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
-- imply
  ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_insideSourceWitness gamma gamma' omega hfg

/--
[rlc_twoChannelFullPhysical_boundary_insideSourceWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_insideSourceWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g f' g' : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hfg' : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f' g') :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p'), sharedPrimalEdge f g = s(p, q) ∧ sharedPrimalEdge f' g' = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ ∀ z ∈ w.support, z ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ z ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_insideSourceWalk gamma gamma' omega hfg hfg'

/--
[rlc_twoChannelFullAmbientConfig_open_source_or_originalTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullAmbientConfig_open_source_or_originalTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {e : Sym2 (Site 2)}
-- given
  (hopen : rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true) :
-- imply
  (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = e) ∨ e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullAmbientConfig_open_source_or_originalTrace gamma gamma' omega hopen

/--
[rlc_twoChannelFullPhysical_boundary_insideOpenSourceWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_insideOpenSourceWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g f' g' : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hfg' : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f' g') :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p'), sharedPrimalEdge f g = s(p, q) ∧ sharedPrimalEdge f' g' = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (∀ z ∈ w.support, z ∈ rlc_twoChannelFullReachSet gamma gamma' omega) ∧ ∀ e ∈ w.edges, rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_insideOpenSourceWalk gamma gamma' omega hfg hfg'

/--
[rlc_flankFaces_eq_of_sharedPrimalEdge_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_flankFaces_eq_of_sharedPrimalEdge_eq_eq
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q)) :
-- imply
  flankFaces p q = s(f, g) := by
-- proof
  apply StatMech.Universality.rlc_flankFaces_eq_of_sharedPrimalEdge_eq hfg hshared

/--
[rlc_doubleDualShift_endpoint_mem_boundaryEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_doubleDualShift_endpoint_mem_boundaryEdge_eq
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hshared : sharedPrimalEdge f g = s(p, q)) :
-- imply
  phb_doubleDualShift p ∈ s(f, g) ∨ phb_doubleDualShift q ∈ s(f, g) := by
-- proof
  apply StatMech.Universality.rlc_doubleDualShift_endpoint_mem_boundaryEdge hfg hpq hshared

/--
[rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry_eq
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q)) :
-- imply
  (g = ![f 0 + 1, f 1] ∧ ((phb_doubleDualShift p = f ∧ phb_doubleDualShift q = ![f 0, f 1 - 1]) ∨ (phb_doubleDualShift p = ![f 0, f 1 - 1] ∧ phb_doubleDualShift q = f))) ∨ (g = ![f 0 - 1, f 1] ∧ ((phb_doubleDualShift p = g ∧ phb_doubleDualShift q = ![f 0 - 1, f 1 - 1]) ∨ (phb_doubleDualShift p = ![f 0 - 1, f 1 - 1] ∧ phb_doubleDualShift q = g))) ∨ (g = ![f 0, f 1 + 1] ∧ ((phb_doubleDualShift p = f ∧ phb_doubleDualShift q = ![f 0 - 1, f 1]) ∨ (phb_doubleDualShift p = ![f 0 - 1, f 1] ∧ phb_doubleDualShift q = f))) ∨ (g = ![f 0, f 1 - 1] ∧ ((phb_doubleDualShift p = g ∧ phb_doubleDualShift q = ![f 0 - 1, f 1 - 1]) ∨ (phb_doubleDualShift p = ![f 0 - 1, f 1 - 1] ∧ phb_doubleDualShift q = g))) := by
-- proof
  apply StatMech.Universality.rlc_sharedPrimalEdge_doubleDualShift_endpoint_geometry hfg hshared

/--
[rlc_sharedPrimalEdge_endpoint_horizontal_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_sharedPrimalEdge_endpoint_horizontal_bounds_eq
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q)) :
-- imply
  f 0 ≤ p 0 ∧ p 0 ≤ f 0 + 1 ∧ f 0 ≤ q 0 ∧ q 0 ≤ f 0 + 1 := by
-- proof
  apply StatMech.Universality.rlc_sharedPrimalEdge_endpoint_horizontal_bounds hfg hshared

/--
[rlc_walk_secondFace_to_doubleDualShift_firstEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_secondFace_to_doubleDualShift_firstEndpoint_eq
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q)) :
-- imply
  ∃ P : (hypercubicLattice 2).Walk g (phb_doubleDualShift p), ∀ z ∈ P.support, z = g ∨ z = f ∨ z = phb_doubleDualShift p := by
-- proof
  apply StatMech.Universality.rlc_walk_secondFace_to_doubleDualShift_firstEndpoint hfg hshared

/--
[rlc_walk_secondFace_to_doubleDualShift_firstEndpoint_with_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_secondFace_to_doubleDualShift_firstEndpoint_with_incidence_eq
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hshared : sharedPrimalEdge f g = s(p, q)) :
-- imply
  ∃ P : (hypercubicLattice 2).Walk g (phb_doubleDualShift p), (∀ z ∈ P.support, z = g ∨ z = f ∨ z = phb_doubleDualShift p) ∧ (phb_doubleDualShift q ∈ s(f, g) → phb_doubleDualShift q ∈ P.support) := by
-- proof
  apply StatMech.Universality.rlc_walk_secondFace_to_doubleDualShift_firstEndpoint_with_incidence hfg hshared

/--
[rlc_doubleDualShiftWalk_between_boundaryEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_doubleDualShiftWalk_between_boundaryEdges_eq
  {p q p' q' f g f' g' : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
-- given
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hstart : phb_doubleDualShift p ∈ s(f, g) ∨ phb_doubleDualShift q ∈ s(f, g))
  (hend : phb_doubleDualShift p' ∈ s(f', g') ∨ phb_doubleDualShift q' ∈ s(f', g')) :
-- imply
  ∃ (a b : Site 2) (W : (hypercubicLattice 2).Walk a b), a ∈ s(f, g) ∧ b ∈ s(f', g') ∧ (a = phb_doubleDualShift p ∨ a = phb_doubleDualShift q) ∧ (b = phb_doubleDualShift p' ∨ b = phb_doubleDualShift q') ∧ ∀ z ∈ W.support, z = phb_doubleDualShift q ∨ z = phb_doubleDualShift q' ∨ ∃ v ∈ w.support, phb_doubleDualShift v = z := by
-- proof
  apply StatMech.Universality.rlc_doubleDualShiftWalk_between_boundaryEdges w hpq hpq' hstart hend

/--
[rlc_doubleDualShift_mem_translatedRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_doubleDualShift_mem_translatedRect_eq
  {alpha beta bottom top : Int}
  {p : Site 2}
-- given
  (hp : p ∈ rect alpha beta bottom top) :
-- imply
  phb_doubleDualShift p ∈ rect (alpha - 1) (beta - 1) (bottom - 1) (top - 1) := by
-- proof
  apply StatMech.Universality.rlc_doubleDualShift_mem_translatedRect hp

/--
[rlc_doubleDualShift_neighbor_mem_expandedRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_doubleDualShift_neighbor_mem_expandedRect_eq
  {alpha beta bottom top : Int}
  {p q : Site 2}
-- given
  (hp : p ∈ rect alpha beta bottom top)
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  phb_doubleDualShift q ∈ rect (alpha - 2) beta (bottom - 2) top := by
-- proof
  apply StatMech.Universality.rlc_doubleDualShift_neighbor_mem_expandedRect hp hpq

/--
[rlc_orientedBoundaryWitness_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_orientedBoundaryWitness_unique_eq
  {H : Set (Site 2)}
  {p q r s : Site 2}
-- given
  (hp : p ∈ H)
  (hs : s ∉ H)
  (heq : s(p, q) = s(r, s)) :
-- imply
  p = r ∧ q = s := by
-- proof
  apply StatMech.Universality.rlc_orientedBoundaryWitness_unique hp hs heq

/--
[rlc_walk_between_tethers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_between_tethers_eq
  {a b t u : Site 2}
  {W : (hypercubicLattice 2).Walk a b}
-- given
  (ha : a = t ∨ (hypercubicLattice 2).Adj a t)
  (hb : b = u ∨ (hypercubicLattice 2).Adj b u) :
-- imply
  ∃ W' : (hypercubicLattice 2).Walk t u, ∀ z ∈ W'.support, z = t ∨ z = u ∨ z ∈ W.support := by
-- proof
  apply StatMech.Universality.rlc_walk_between_tethers W ha hb

/--
[rlc_neighbor_mem_expandedRect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_neighbor_mem_expandedRect_eq
  {alpha beta bottom top : Int}
  {p q : Site 2}
-- given
  (hp : p ∈ rect alpha beta bottom top)
  (hpq : (hypercubicLattice 2).Adj p q) :
-- imply
  q ∈ rect (alpha - 1) (beta + 1) (bottom - 1) (top + 1) := by
-- proof
  apply StatMech.Universality.rlc_neighbor_mem_expandedRect hp hpq

/--
[rlc_twoChannelFullPhysical_goodComponent_or_classifiedBadSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodComponent_or_classifiedBadSeparation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨ RlcTwoChannelFullPhysicalClassifiedBadCarrierSeparation gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodComponent_or_classifiedBadSeparation gamma gamma' hfaith omega hno

/--
[rlc_faceBoundary_orderedContact_of_flippedTraceWalk_exit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_faceBoundary_orderedContact_of_flippedTraceWalk_exit_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d}
  {H : Set (Site 2)}
  {u z : Site 2}
  {p : (hypercubicLattice 2).Walk (rlc_flipX u) (rlc_flipX z)}
-- given
  (hpTrace : ∀ v ∈ p.support, ∃ w ∈ rlc_pathVertices tau, rlc_flipX w = v)
  (huIn : rlc_flipX u ∈ H)
  (hzOut : rlc_flipX z ∉ H) :
-- imply
  ∃ x : Site 2, x ∈ (faceBoundaryGraph H).support ∧ rlc_dualReflect x ∈ rlc_pathVertices tau ∧ rlc_flipX (rlc_dualReflect x) ∈ p.support := by
-- proof
  apply StatMech.Universality.rlc_faceBoundary_orderedContact_of_flippedTraceWalk_exit tau H p hpTrace huIn hzOut

/--
[rlc_exists_last_bookFlippedTraceIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exists_last_bookFlippedTraceIntersection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ z : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'), ∀ q : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'), rlc_bookFlippedTraceIntersectionRank gamma gamma' q ≤ rlc_bookFlippedTraceIntersectionRank gamma gamma' z := by
-- proof
  apply StatMech.Universality.rlc_exists_last_bookFlippedTraceIntersection gamma gamma' hfaith

/--
[rlc_bookLastFlippedTraceIntersection_of_faithful](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookLastFlippedTraceIntersection_of_faithful_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ (z : Site 2) (hz : z ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma'), z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ ∀ q : ↑(rlc_bookFlippedTraceIntersectionSet gamma gamma'), rlc_bookFlippedTraceIntersectionRank gamma gamma' q ≤ rlc_bookFlippedTraceIntersectionRank gamma gamma' ⟨z, hz⟩ := by
-- proof
  apply StatMech.Universality.rlc_bookLastFlippedTraceIntersection_of_faithful gamma gamma' hfaith

/--
[rlc_idxOf_le_of_mem_takeUntil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_idxOf_le_of_mem_takeUntil_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b z q : V}
  {W : G.Walk a b}
-- given
  (hz : z ∈ W.support)
  (hq : q ∈ (W.takeUntil z hz).support) :
-- imply
  W.support.idxOf q ≤ W.support.idxOf z := by
-- proof
  apply StatMech.Universality.rlc_idxOf_le_of_mem_takeUntil W hz hq

/--
[rlc_mem_takeUntil_iff_idxOf_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_mem_takeUntil_iff_idxOf_le_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b z q : V}
  {W : G.Walk a b}
-- given
  (hz : z ∈ W.support)
  (hq : q ∈ W.support) :
-- imply
  q ∈ (W.takeUntil z hz).support ↔ W.support.idxOf q ≤ W.support.idxOf z := by
-- proof
  apply StatMech.Universality.rlc_mem_takeUntil_iff_idxOf_le W hz hq

/--
[rlc_isPath_mem_dropUntil_iff_idxOf_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_isPath_mem_dropUntil_iff_idxOf_le_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b z q : V}
  {W : G.Walk a b}
-- given
  (hW : W.IsPath)
  (hz : z ∈ W.support)
  (hq : q ∈ W.support) :
-- imply
  q ∈ (W.dropUntil z hz).support ↔ W.support.idxOf z ≤ W.support.idxOf q := by
-- proof
  apply StatMech.Universality.rlc_isPath_mem_dropUntil_iff_idxOf_le W hW hz hq

/--
[rlc_walk_exists_last_lower_first_upper_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_exists_last_lower_first_upper_contact_eq
  {G : SimpleGraph V}
  {a b : V}
  {W : G.Walk a b}
  {i0 j0 : Nat}
-- given
  (lower upper : V → Prop)
  (hi0j0 : i0 ≤ j0)
  (hj0Length : j0 ≤ W.length)
  (hi0Lower : lower (W.getVert i0))
  (hj0Upper : upper (W.getVert j0)) :
-- imply
  ∃ i j : Nat, i0 ≤ i ∧ i ≤ j ∧ j ≤ j0 ∧ j0 ≤ W.length ∧ lower (W.getVert i) ∧ upper (W.getVert j) ∧ (∀ k : Nat, k ≤ j0 → lower (W.getVert k) → k ≤ i) ∧ (∀ k : Nat, i ≤ k → k ≤ j0 → upper (W.getVert k) → j ≤ k) := by
-- proof
  apply StatMech.Universality.rlc_walk_exists_last_lower_first_upper_contact W lower upper hi0j0 hj0Length hi0Lower hj0Upper

/--
[rlc_collaredVerticalArc_meets_leftRightWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_collaredVerticalArc_meets_leftRightWalk_eq
  {alpha beta bottom top : Int}
  {x y a b : Site 2}
  {V : (hypercubicLattice 2).Walk x y}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hab : alpha < beta)
  (hbt : bottom ≤ top)
  (hxBox : x ∈ rect alpha beta bottom top)
  (hyBox : y ∈ rect alpha beta bottom top)
  (hVBox : ∀ z ∈ V.support, z ∈ rect alpha beta bottom top)
  (haBox : a ∈ rect alpha beta bottom top)
  (hbBox : b ∈ rect alpha beta bottom top)
  (haLeft : a 0 = alpha)
  (hbRight : b 0 = beta)
  (hHBox : ∀ z ∈ H.support, z ∈ rect alpha beta bottom top)
  (hpre : ∀ z ∈ H.support, z ∈ (sw_vertSeg (x 0) bottom (x 1)).support → z ∈ V.support)
  (hpost : ∀ z ∈ H.support, z ∈ (sw_vertSeg (y 0) (y 1) top).support → z ∈ V.support) :
-- imply
  ∃ z ∈ H.support, z ∈ V.support := by
-- proof
  apply StatMech.Universality.rlc_collaredVerticalArc_meets_leftRightWalk hab hbt hxBox hyBox V hVBox H haBox hbBox haLeft hbRight hHBox hpre hpost

/--
[rlc_twoChannelFullPhysical_not_cyclicOrderCrossingCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_not_cyclicOrderCrossingCertificate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {C : RlcTwoChannelFullPhysicalCyclicOrderCrossingCertificate gamma gamma' omega} :
-- imply
  False := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_not_cyclicOrderCrossingCertificate C

/--
[rlc_bookRightIntersectionRank_strict_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRightIntersectionRank_strict_of_ne_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z r : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hrRight : r ∈ rlc_pathVertices gamma.1)
  (hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1)
  (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
  (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
  (hrz : r ≠ z) :
-- imply
  right.length < (rlc_ambientCrossingWalk gamma.1).support.idxOf r := by
-- proof
  apply StatMech.Universality.rlc_bookRightIntersectionRank_strict_of_ne right hzRight hrRight hrLeft hrank hmin hrz

/--
[rlc_twoChannelFullPhysical_leftContact_reflectedRight_rank_progress](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_leftContact_reflectedRight_rank_progress_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z y u : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y u}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hyLeft : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
  (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (huRight : ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect u = rlc_flipX r) :
-- imply
  ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect y = rlc_flipX r ∧ r ∈ flipLeft.support ∧ (r = z ∨ right.length < (rlc_ambientCrossingWalk gamma.1).support.idxOf r) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_leftContact_reflectedRight_rank_progress right flipLeft q hzRight hyLeft hyOrder hrank hmin hedges huRight

/--
[RlcBookFaithfulTracePair.intersection_ne_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma intersection_ne_flip_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
-- imply
  z ≠ rlc_flipX z := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.intersection_ne_flip hfaith hzRight hzLeft

/--
[RlcBookFaithfulTracePair.intersection_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma intersection_positive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
-- imply
  0 < z 0 := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.intersection_positive hfaith hzRight hzLeft

/--
[rlc_bookShiftedOuterTrace_bridge_endpoints_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookShiftedOuterTrace_bridge_endpoints_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
-- imply
  rlc_dualReflect.symm z ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧ rlc_dualReflect.symm (rlc_flipX z) ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support := by
-- proof
  apply StatMech.Universality.rlc_bookShiftedOuterTrace_bridge_endpoints_mem gamma gamma' hzRight hzLeft

/--
[rlc_bookShiftedOuterTrace_forced_contacts_mem_orderedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookShiftedOuterTrace_forced_contacts_mem_orderedArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y z : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxEq : rlc_dualReflect x = z)
  (hyEq : rlc_dualReflect y = rlc_flipX z) :
-- imply
  (x ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧ x ∈ (rlc_orderedContourArc c hx hy).support) ∧ (y ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧ y ∈ (rlc_orderedContourArc c hx hy).support) := by
-- proof
  apply StatMech.Universality.rlc_bookShiftedOuterTrace_forced_contacts_mem_orderedArc c hx hy hzRight hzLeft hxEq hyEq

/--
[rlc_bookShiftedOuterTrace_forced_contacts_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookShiftedOuterTrace_forced_contacts_distinct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y z : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxEq : rlc_dualReflect x = z)
  (hyEq : rlc_dualReflect y = rlc_flipX z) :
-- imply
  ((x ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧ x ∈ (rlc_orderedContourArc c hx hy).support) ∧ (y ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧ y ∈ (rlc_orderedContourArc c hx hy).support)) ∧ x ≠ y := by
-- proof
  apply StatMech.Universality.rlc_bookShiftedOuterTrace_forced_contacts_distinct hfaith c hx hy hzRight hzLeft hxEq hyEq

/--
[rlc_bookShiftedInnerTrace_contacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookShiftedInnerTrace_contacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support) :
-- imply
  x ∈ (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).support ∧ y ∈ (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).support := by
-- proof
  apply StatMech.Universality.rlc_bookShiftedInnerTrace_contacts right flipLeft hxOrder hyOrder

/--
[rlc_bookShiftedInnerTrace_contact_indices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookShiftedInnerTrace_contact_indices_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support) :
-- imply
  ∃ i j : Nat, i ≤ j ∧ j ≤ (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).length ∧ (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).getVert i = x ∧ (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).getVert j = y := by
-- proof
  apply StatMech.Universality.rlc_bookShiftedInnerTrace_contact_indices hfaith right flipLeft hzRight hzLeft hxOrder hyOrder

/--
[rlc_bookShiftedOuterCoreTrace_mem_faceBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookShiftedOuterCoreTrace_mem_faceBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z v : Site 2}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hv : v ∈ (rlc_bookShiftedOuterCoreTrace gamma gamma' hzRight hzLeft).support) :
-- imply
  v ∈ rect (-2 * n - 1) (2 * n) (-n - 1) n := by
-- proof
  apply StatMech.Universality.rlc_bookShiftedOuterCoreTrace_mem_faceBox gamma gamma' hzRight hzLeft hv

/--
[rlc_bookShiftedOuterTrace_mem_faceBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookShiftedOuterTrace_mem_faceBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z v : Site 2}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hv : v ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support) :
-- imply
  v ∈ rect (-2 * n - 1) (2 * n) (-n - 1) n := by
-- proof
  apply StatMech.Universality.rlc_bookShiftedOuterTrace_mem_faceBox gamma gamma' hzRight hzLeft hv

/--
[rlc_bookShiftedOuterTrace_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookShiftedOuterTrace_support_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z v : Site 2}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hv : v ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support) :
-- imply
  (∃ w ∈ rlc_pathVertices gamma.1, v = rlc_dualReflect.symm w) ∨ (∃ t : Int, t ∈ Set.uIcc (-z 0 - 1) (z 0 - 1) ∧ v = ![t, z 1 - 1]) ∨ (∃ w ∈ rlc_pathVertices gamma'.1, v = rlc_dualReflect.symm w) ∨ ∃ t : Int, t ∈ Set.uIcc ((rlc_dualReflect.symm (gamma'.1.1 : Site 2)) 0) (2 * n) ∧ v = ![t, (rlc_dualReflect.symm (gamma'.1.1 : Site 2)) 1] := by
-- proof
  apply StatMech.Universality.rlc_bookShiftedOuterTrace_support_cases gamma gamma' hzRight hzLeft hv

/--
[rlc_bookShiftedOuterTrace_start_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookShiftedOuterTrace_start_left_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n} :
-- imply
  (rlc_dualReflect.symm (gamma.1.2.1 : Site 2)) 0 = -2 * n - 1 := by
-- proof
  apply StatMech.Universality.rlc_bookShiftedOuterTrace_start_left gamma

/--
[rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hcycle : c.IsCycle)
  (hv : v ∈ c.support) :
-- imply
  v ∈ rect (-2 * n - 1) (2 * n) (-n - 1) n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox hn gamma gamma' omega c hcycle hv

/--
[rlc_twoChannelFullPhysical_intersectionImage_contacts_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_intersectionImage_contacts_ne_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hx : rlc_dualReflect x = z)
  (hy : rlc_dualReflect y = rlc_flipX z) :
-- imply
  x ≠ y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_intersectionImage_contacts_ne hfaith hzRight hzLeft hx hy

/--
[rlc_bookOrderedCandidateReverseRank_lt_of_rightRank_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookOrderedCandidateReverseRank_lt_of_rightRank_lt_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z q : Site 2}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hqCandidate : q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzq : (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q) :
-- imply
  rlc_bookOrderedCandidateReverseRank gamma q < rlc_bookOrderedCandidateReverseRank gamma z := by
-- proof
  apply StatMech.Universality.rlc_bookOrderedCandidateReverseRank_lt_of_rightRank_lt hzCandidate hqCandidate hzq

/--
[rlc_bookFirstIntersection_mem_orderedCandidateSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookFirstIntersection_mem_orderedCandidateSet_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
  (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right) :
-- imply
  z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_bookFirstIntersection_mem_orderedCandidateSet right hzRight hzLeft hrank hmin

/--
[rlc_bookOrderedIntersectionCandidate_rightRank_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookOrderedIntersectionCandidate_rightRank_strict_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z r : Site 2}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
  (hzrLeft : (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤ (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX r))
  (hrz : r ≠ z) :
-- imply
  (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf r := by
-- proof
  apply StatMech.Universality.rlc_bookOrderedIntersectionCandidate_rightRank_strict hzCandidate hrSet hzrLeft hrz

/--
[rlc_bookOrderedIntersectionCandidates_order_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookOrderedIntersectionCandidates_order_agree_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z q : Site 2}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hqCandidate : q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma') :
-- imply
  ((rlc_ambientCrossingWalk gamma.1).support.idxOf q < (rlc_ambientCrossingWalk gamma.1).support.idxOf z) ↔ ((rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX q) < (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z)) := by
-- proof
  apply StatMech.Universality.rlc_bookOrderedIntersectionCandidates_order_agree hzCandidate hqCandidate

/--
[rlc_bookOrderedIntersectionCandidate_exists_later](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookOrderedIntersectionCandidate_exists_later_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z r : Site 2}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
  (hzrLeft : (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤ (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX r))
  (hrz : r ≠ z) :
-- imply
  ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧ (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf r := by
-- proof
  apply StatMech.Universality.rlc_bookOrderedIntersectionCandidate_exists_later hzCandidate hrSet hzrLeft hrz

/--
[rlc_bookOrderedIntersectionCandidate_exists_earlier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookOrderedIntersectionCandidate_exists_earlier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z r : Site 2}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
  (hrzRight : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
  (hrz : r ≠ z) :
-- imply
  ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf r ∧ (rlc_ambientCrossingWalk gamma.1).support.idxOf q < (rlc_ambientCrossingWalk gamma.1).support.idxOf z := by
-- proof
  apply StatMech.Universality.rlc_bookOrderedIntersectionCandidate_exists_earlier hzCandidate hrSet hrzRight hrz

/--
[rlc_exists_max_bookOrderedIntersectionCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exists_max_bookOrderedIntersectionCandidate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z := by
-- proof
  apply StatMech.Universality.rlc_exists_max_bookOrderedIntersectionCandidate gamma gamma' hfaith

/--
[rlc_exists_min_bookOrderedIntersectionCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exists_min_bookOrderedIntersectionCandidate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  ∃ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf q := by
-- proof
  apply StatMech.Universality.rlc_exists_min_bookOrderedIntersectionCandidate gamma gamma' hfaith

/--
[rlc_bookMaxOrderedIntersectionCandidate_eq_of_leftLater](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookMaxOrderedIntersectionCandidate_eq_of_leftLater_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z r : Site 2}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzMax : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
  (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
  (hzrLeft : (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX z) ≤ (rlc_ambientCrossingWalk gamma'.1).support.idxOf (rlc_flipX r)) :
-- imply
  r = z := by
-- proof
  apply StatMech.Universality.rlc_bookMaxOrderedIntersectionCandidate_eq_of_leftLater hzCandidate hzMax hrSet hzrLeft

/--
[rlc_bookMinOrderedIntersectionCandidate_eq_of_rightEarlier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookMinOrderedIntersectionCandidate_eq_of_rightEarlier_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z r : Site 2}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzMin : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf q)
  (hrSet : r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma')
  (hrzRight : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z) :
-- imply
  r = z := by
-- proof
  apply StatMech.Universality.rlc_bookMinOrderedIntersectionCandidate_eq_of_rightEarlier hzCandidate hzMin hrSet hrzRight

/--
[rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ (x y : Site 2) (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)), x ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support ∧ y ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support ∧ rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧ RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧ RlcBookRightIntersectionRankRealizedAt gamma right ∧ RlcBookRightPrefixRankAt gamma right := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_orderedContacts_at_intersection_of_failure gamma gamma' hfaith omega hno z hzRight hzLeft

/--
[rlc_twoChannelFullPhysical_leftContact_reflectedRight_candidateProgress](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_leftContact_reflectedRight_candidateProgress_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z y u : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y u}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hyLeft : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (huRight : ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect u = rlc_flipX r) :
-- imply
  ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect y = rlc_flipX r ∧ r ∈ flipLeft.support ∧ (r = z ∨ (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf r) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_leftContact_reflectedRight_candidateProgress flipLeft q hzCandidate hyLeft hyOrder hflipLeftRank hedges huRight

/--
[rlc_twoChannelFullPhysical_leftContact_reflectedRight_eq_of_maxCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_leftContact_reflectedRight_eq_of_maxCandidate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z y u : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y u}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzMax : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
  (hyLeft : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (huRight : ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect u = rlc_flipX r) :
-- imply
  rlc_dualReflect y = rlc_flipX z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_leftContact_reflectedRight_eq_of_maxCandidate flipLeft q hzCandidate hzMax hyLeft hyOrder hflipLeftRank hedges huRight

/--
[rlc_twoChannelFullPhysical_maxCandidate_reflectedRight_contacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_maxCandidate_reflectedRight_contacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y u : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzMax : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
  (hx : rlc_dualReflect x = z)
  (hyLeft : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (huRight : ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect u = rlc_flipX r) :
-- imply
  rlc_dualReflect y = rlc_flipX z ∧ x ≠ y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_maxCandidate_reflectedRight_contacts hfaith flipLeft q hzCandidate hzMax hx hyLeft hyOrder hflipLeftRank hedges huRight

/--
[rlc_twoChannelFullPhysical_rightContact_reflectedLeft_candidateRetreat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rightContact_reflectedLeft_candidateRetreat_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x u : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hxRight : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (huLeft : ∃ l ∈ rlc_pathVertices gamma'.1, rlc_dualReflect u = rlc_flipX l) :
-- imply
  ∃ r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma', rlc_dualReflect x = r ∧ (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧ (r = z ∨ ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf r ∧ (rlc_ambientCrossingWalk gamma.1).support.idxOf q < (rlc_ambientCrossingWalk gamma.1).support.idxOf z) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rightContact_reflectedLeft_candidateRetreat right q hzCandidate hxRight hxOrder hrightPrefix hedges huLeft

/--
[rlc_twoChannelFullPhysical_rightContact_reflectedLeft_eq_of_minCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rightContact_reflectedLeft_eq_of_minCandidate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x u : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzMin : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf q)
  (hxRight : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
  (hedges : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (huLeft : ∃ l ∈ rlc_pathVertices gamma'.1, rlc_dualReflect u = rlc_flipX l) :
-- imply
  rlc_dualReflect x = z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rightContact_reflectedLeft_eq_of_minCandidate right q hzCandidate hzMin hxRight hxOrder hrightPrefix hedges huLeft

/--
[rlc_twoChannelFullPhysical_firstIntersectionOrderedContacts_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_firstIntersectionOrderedContacts_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalFirstIntersectionOrderedContacts gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_firstIntersectionOrderedContacts_of_failure gamma gamma' hfaith omega hno

/--
[rlc_twoChannelFullPhysical_goodComponent_or_firstIntersectionOrderedBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodComponent_or_firstIntersectionOrderedBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega ∨ RlcTwoChannelFullPhysicalFirstIntersectionOrderedBadSeparation gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodComponent_or_firstIntersectionOrderedBad gamma gamma' hfaith omega hno

/--
[rlc_isCycles_isPath_eq_of_snd_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_isCycles_isPath_eq_of_snd_eq_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : V}
  {p q : G.Walk x y}
-- given
  (hcycles : G.IsCycles)
  (hpPath : p.IsPath)
  (hqPath : q.IsPath)
  (hxy : x ≠ y)
  (hsnd : p.snd = q.snd) :
-- imply
  p = q := by
-- proof
  apply StatMech.Universality.rlc_isCycles_isPath_eq_of_snd_eq hcycles p q hpPath hqPath hxy hsnd

/--
[rlc_isCycles_isPath_eq_ordered_or_complementary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_isCycles_isPath_eq_ordered_or_complementary_eq
  {H : SimpleGraph (Site 2)}
  {u x y : Site 2}
  {c : H.Walk u u}
  {p : H.Walk x y}
-- given
  (hcycles : H.IsCycles)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxy : x ≠ y)
  (hp : p.IsPath) :
-- imply
  p = rlc_orderedContourArc c hx hy ∨ p = rlc_complementaryContourArc c hx hy := by
-- proof
  apply StatMech.Universality.rlc_isCycles_isPath_eq_ordered_or_complementary hcycles c hc hx hy hxy p hp

/--
[rlc_twoChannelFullPhysical_contactCycle_of_boundaryContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_of_boundaryContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
-- given
  (hxSupport : x ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (hySupport : y ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u), c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_of_boundaryContacts gamma gamma' omega hxSupport hySupport

/--
[rlc_twoChannelFullPhysical_contactCycle_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_covers_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (hxSupport : x ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (hxCycle : x ∈ c.support) :
-- imply
  ∀ e ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_covers gamma gamma' omega c hcycle hxSupport hxCycle

/--
[rlc_twoChannelFullPhysical_contactCycle_support_of_boundarySupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_support_of_boundarySupport_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a v : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (haSupport : a ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (haCycle : a ∈ c.support)
  (hvSupport : v ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  v ∈ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_support_of_boundarySupport gamma gamma' omega c hcycle haSupport haCycle hvSupport

/--
[rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (hxSupport : x ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (hxCycle : x ∈ c.support) :
-- imply
  rlc_twoChannelFullFilledReachSet gamma gamma' omega = jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion gamma gamma' omega c hcycle hxSupport hxCycle

/--
[rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle) :
-- imply
  rlc_twoChannelFullFilledReachSet gamma gamma' omega = jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_filledReachSet_eq_leftRegion_of_cycle gamma gamma' omega c hcycle

/--
[rlc_twoChannelFullPhysical_boundary_leftRegionTransition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_leftRegionTransition_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (hxSupport : x ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (hxCycle : x ∈ c.support)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g) :
-- imply
  ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧ q ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧ (p ∈ (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support ∨ q ∈ (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_leftRegionTransition gamma gamma' omega c hcycle hxSupport hxCycle hfg

/--
[rlc_twoChannelFullPhysical_boundary_insideSourceWalk_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_insideSourceWalk_leftRegion_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u f g f' g' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (hxSupport : x ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (hxCycle : x ∈ c.support)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hfg' : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f' g') :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p'), sharedPrimalEdge f g = s(p, q) ∧ sharedPrimalEdge f' g' = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ q ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧ q' ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧ (∀ z ∈ w.support, z ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧ (p ∈ (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support ∨ q ∈ (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support) ∧ (p' ∈ (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support ∨ q' ∈ (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_insideSourceWalk_leftRegion gamma gamma' omega c hcycle hxSupport hxCycle hfg hfg'

/--
[rlc_twoChannelFullPhysical_firstIntersectionContactCycle_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_firstIntersectionContactCycle_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ∃ (z x y u : Site 2) (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u), c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support ∧ z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support ∧ rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧ RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧ (∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z) ∧ RlcBookRightIntersectionRankRealizedAt gamma right ∧ RlcBookRightIntersectionRankMinimalAt gamma gamma' right := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_firstIntersectionContactCycle_of_failure gamma gamma' hfaith omega hno

/--
[rlc_twoChannelFullPhysical_contactCycle_of_faithful_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_of_faithful_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  ∃ (x y u : Site 2) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u), c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_of_faithful_failure gamma gamma' hfaith omega hno

/--
[rlc_twoChannelFullPhysical_contactCycle_of_staticCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contactCycle_of_staticCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) :
-- imply
  ∃ (x y u : Site 2) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u), c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contactCycle_of_staticCut gamma gamma' hfaith A hAright hAleft

/--
[rlc_twoChannelFullPhysical_contourArcSide_iff_badEdgesOnOneArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contourArcSide_iff_badEdgesOnOneArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support) :
-- imply
  RlcTwoChannelFullPhysicalContourArcSide gamma gamma' omega c hx hy ↔ RlcTwoChannelFullPhysicalBadEdgesOnOneArcAt gamma gamma' omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contourArcSide_iff_badEdgesOnOneArc gamma gamma' omega c hc hx hy

/--
[rlc_twoChannelFullPhysical_goodReachable_of_carriedBoundaryWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodReachable_of_carriedBoundaryWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {a : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y}
-- given
  (hcarried : ∀ {f g : Site 2}, s(f, g) ∈ a.edges → RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
-- imply
  (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodReachable_of_carriedBoundaryWalk gamma gamma' omega a hcarried

/--
[rlc_twoChannelFullPhysical_goodReachable_of_repairedBoundaryWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodReachable_of_repairedBoundaryWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {a : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y}
-- given
  (hrepair : ∀ {f g : Site 2}, s(f, g) ∈ a.edges → (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable f g) :
-- imply
  (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodReachable_of_repairedBoundaryWalk gamma gamma' omega a hrepair

/--
[rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'} :
-- imply
  rlc_twoChannelFullPhysicalRepairableBoundaryGraph gamma gamma' omega ≤ faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le gamma gamma' omega

/--
[rlc_twoChannelFullPhysical_goodReachable_of_repairableBoundaryWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodReachable_of_repairableBoundaryWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {q : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph gamma gamma' omega).Walk x y} :
-- imply
  (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodReachable_of_repairableBoundaryWalk gamma gamma' omega q

/--
[rlc_twoChannelFullPhysical_contourArcRepairSide_of_contourArcSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_contourArcRepairSide_of_contourArcSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hside : RlcTwoChannelFullPhysicalContourArcSide gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalContourArcRepairSide gamma gamma' omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_contourArcRepairSide_of_contourArcSide gamma gamma' omega c hx hy hside

/--
[rlc_twoChannelFullPhysical_goodComponent_of_contourArcRepairSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodComponent_of_contourArcRepairSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSide gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodComponent_of_contourArcRepairSide gamma gamma' omega c hx hy hxPath hyPath hrepair

/--
[rlc_twoChannelFullPhysical_goodComponent_of_contourArcSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodComponent_of_contourArcSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hside : RlcTwoChannelFullPhysicalContourArcSide gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodComponent_of_contourArcSide gamma gamma' omega c hx hy hxPath hyPath hside

/--
[rlc_twoChannelFullPhysical_twoArcFirstBad_of_not_contourArcSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcFirstBad_of_not_contourArcSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hbadSide : ¬RlcTwoChannelFullPhysicalContourArcSide gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcFirstBadAt gamma gamma' omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcFirstBad_of_not_contourArcSide gamma gamma' omega c hc hx hy hbadSide

/--
[rlc_twoChannelFullPhysical_faithful_twoArcFirstBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_faithful_twoArcFirstBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hbadSide : ¬RlcTwoChannelFullPhysicalContourArcSide gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcFirstBadAt gamma gamma' omega c hx hy ∧ ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧ ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_faithful_twoArcFirstBad hfaith omega c hc hx hy hxPath hyPath hbadSide

/--
[rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_firstBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_firstBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hbad : RlcTwoChannelFullPhysicalTwoArcFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcBadTerminalPlacementAt gamma gamma' omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_firstBad hbad

/--
[rlc_twoChannelFullPhysical_faithful_twoArcClassifiedFirstBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_faithful_twoArcClassifiedFirstBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hc : c.IsTrail)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hbadSide : ¬RlcTwoChannelFullPhysicalContourArcSide gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcClassifiedFirstBadAt gamma gamma' omega c hx hy ∧ ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧ ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_faithful_twoArcClassifiedFirstBad hfaith omega c hc hx hy hxPath hyPath hbadSide

/--
[rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hfirst : ∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
  (hallR : ∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hallL : ∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hurLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ur) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ur))
  (hulLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ul) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ul)) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcWallFamilyTruthTable gamma gamma' omega flipLeft qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable hfaith right flipLeft qr ql hxPath hyPath hxOrder hyOrder hfirst hallR hallL hurLoc hulLoc

/--
[rlc_twoChannelFullPhysical_twoArc_oppositeAxisWall_end_mem_suffixes_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArc_oppositeAxisWall_end_mem_suffixes_at_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxAxis : rlc_dualReflect x = (gamma.1.1 : Site 2))
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hqrRight : ∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (hqlLeft : ∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) :
-- imply
  ∃ (hzR : rlc_flipX z ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support) (hzL : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support), rlc_dualReflect ur ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hzR).support ∧ rlc_dualReflect ul ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hzL).support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArc_oppositeAxisWall_end_mem_suffixes_at hnoGood hzRight hzLeft qr ql hxAxis hyAxis hqrRight hqlLeft

/--
[rlc_connectorBarrier_original_or_exclusive_strict_reflected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_connectorBarrier_original_or_exclusive_strict_reflected_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hz : z ∈ rlc_connectorBarrier gamma gamma') :
-- imply
  z ∈ rlc_pathVertices gamma.1 ∨ z ∈ rlc_pathVertices gamma'.1 ∨ RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' z ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' z := by
-- proof
  apply StatMech.Universality.rlc_connectorBarrier_original_or_exclusive_strict_reflected gamma gamma' hz

/--
[rlc_rightArcBadLocation_of_not_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_rightArcBadLocation_of_not_exclusive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hbad : RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z)
  (hnot : ¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' z ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' z)) :
-- imply
  z ∈ rlc_pathVertices gamma.1 ∨ z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n := by
-- proof
  apply StatMech.Universality.rlc_rightArcBadLocation_of_not_exclusive hbad hnot

/--
[rlc_leftArcTargetBadLocation_of_not_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_leftArcTargetBadLocation_of_not_exclusive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hbad : RlcTwoChannelFullPhysicalLeftArcTargetBadLocation gamma gamma' z)
  (hnot : ¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' z ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' z)) :
-- imply
  z ∈ rlc_pathVertices gamma'.1 ∨ z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n := by
-- proof
  apply StatMech.Universality.rlc_leftArcTargetBadLocation_of_not_exclusive hbad hnot

/--
[rlc_rightArcClassifiedBad_of_terminal_not_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_rightArcClassifiedBad_of_terminal_not_exclusive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
-- given
  (hclass : RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega u v)
  (hnot : ¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect u) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect u))) :
-- imply
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧ (rlc_dualReflect u ∈ rlc_pathVertices gamma.1 ∨ (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n)) ∨ ∃ p q : Site 2, sharedPrimalEdge u v = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p := by
-- proof
  apply StatMech.Universality.rlc_rightArcClassifiedBad_of_terminal_not_exclusive hclass hnot

/--
[rlc_leftArcClassifiedBad_of_terminal_not_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_leftArcClassifiedBad_of_terminal_not_exclusive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v : Site 2}
-- given
  (hclass : RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega u v)
  (hnot : ¬(RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect u) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect u))) :
-- imply
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧ (rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 ∨ (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n)) ∨ ∃ p q : Site 2, sharedPrimalEdge u v = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p := by
-- proof
  apply StatMech.Universality.rlc_leftArcClassifiedBad_of_terminal_not_exclusive hclass hnot

/--
[rlc_twoChannelFullPhysical_rightArcShiftedBad_endpoint_tether](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rightArcShiftedBad_endpoint_tether_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v a : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hbad : RlcTwoChannelFullPhysicalRightArcShiftedClassifiedBad gamma gamma' omega u v a) :
-- imply
  (∃ t : Site 2, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' (rlc_dualReflect t) ∧ (a = t ∨ (hypercubicLattice 2).Adj a t)) ∨ ∃ p : Site 2, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧ (a = phb_doubleDualShift p ∨ (hypercubicLattice 2).Adj a (phb_doubleDualShift p)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rightArcShiftedBad_endpoint_tether huv hbad

/--
[rlc_twoChannelFullPhysical_leftArcShiftedBad_endpoint_tether](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_leftArcShiftedBad_endpoint_tether_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u v a : Site 2}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hbad : RlcTwoChannelFullPhysicalLeftArcShiftedClassifiedBad gamma gamma' omega u v a) :
-- imply
  (∃ t : Site 2, RlcTwoChannelFullPhysicalLeftArcTargetBadLocation gamma gamma' (rlc_dualReflect t) ∧ (a = t ∨ (hypercubicLattice 2).Adj a t)) ∨ ∃ p : Site 2, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧ (a = phb_doubleDualShift p ∨ (hypercubicLattice 2).Adj a (phb_doubleDualShift p)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_leftArcShiftedBad_endpoint_tether huv hbad

/--
[rlc_twoChannelFullPhysical_twoArcFirstBad_of_noGoodFirstBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcFirstBad_of_noGoodFirstBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcFirstBadAt gamma gamma' omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcFirstBad_of_noGoodFirstBad hbad

/--
[rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_noGoodFirstBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_noGoodFirstBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcBadTerminalPlacementAt gamma gamma' omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcBadTerminalPlacement_of_noGoodFirstBad hbad

/--
[rlc_twoChannelFullPhysical_not_badEdgesOnOneArc_of_twoArcNoGoodFirstBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_not_badEdgesOnOneArc_of_twoArcNoGoodFirstBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hc : c.IsTrail)
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ¬RlcTwoChannelFullPhysicalBadEdgesOnOneArcAt gamma gamma' omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_not_badEdgesOnOneArc_of_twoArcNoGoodFirstBad hc hbad

/--
[rlc_twoChannelFullPhysical_not_contourArcSide_of_twoArcNoGoodFirstBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_not_contourArcSide_of_twoArcNoGoodFirstBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hc : c.IsTrail)
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ¬RlcTwoChannelFullPhysicalContourArcSide gamma gamma' omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_not_contourArcSide_of_twoArcNoGoodFirstBad hc hbad

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_insideSourceWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_insideSourceWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl p q p' q' : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (w : (hypercubicLattice 2).Walk p p'), (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧ s(ur, vr) ≠ s(ul, vl) ∧ RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr ∧ RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl ∧ sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (phb_doubleDualShift p ∈ s(ur, vr) ∨ phb_doubleDualShift q ∈ s(ur, vr)) ∧ (phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' ∈ s(ul, vl)) ∧ ∀ z ∈ w.support, z ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ z ∈ rect (-2 * n) (2 * n) (-n) n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_insideSourceWalk hbad

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_shiftedInsideSourceWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_shiftedInsideSourceWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl a b : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (W : (hypercubicLattice 2).Walk a b), (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧ s(ur, vr) ≠ s(ul, vl) ∧ RlcTwoChannelFullPhysicalRightArcShiftedClassifiedBad gamma gamma' omega ur vr a ∧ RlcTwoChannelFullPhysicalLeftArcShiftedClassifiedBad gamma gamma' omega ul vl b ∧ a ∈ s(ur, vr) ∧ b ∈ s(ul, vl) ∧ (∀ z ∈ W.support, z ∈ rect (-2 * n - 2) (2 * n) (-n - 2) n) ∧ ∀ z ∈ W.support, (∃ v ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift v = z) ∨ ∃ v ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega, phb_doubleDualShift v = z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_shiftedInsideSourceWalk hbad

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (W : (hypercubicLattice 2).Walk ur ul), (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧ s(ur, vr) ≠ s(ul, vl) ∧ ∀ z ∈ W.support, z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk hbad

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk_withDirections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk_withDirections_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x) (W : (hypercubicLattice 2).Walk ur ul) (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr) (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl), rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr) ∧ (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl) ∧ s(ur, vr) ≠ s(ul, vl) ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ur vr ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ul vl ∧ RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr ∧ RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl ∧ ∀ z ∈ W.support, z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_badTerminalWalk_withDirections hbad

/--
[rlc_twoChannelFullPhysical_directedBadTerminalCrossingWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_directedBadTerminalCrossingWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {ur vr ul vl : Site 2}
  {W : (hypercubicLattice 2).Walk ur ul}
-- given
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hWBox : ∀ v ∈ W.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) :
-- imply
  ∃ T : (hypercubicLattice 2).Walk vr vl, ∀ v ∈ T.support, v ∈ rect (-2 * n - 4) (2 * n + 2) (-n - 4) (n + 2) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_directedBadTerminalCrossingWalk W hurv hulv hWBox

/--
[rlc_twoChannelFullPhysical_boundary_directedSourceWalk_withProvenance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_directedSourceWalk_withProvenance_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {ur vr ul vl : Site 2}
-- given
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (T : (hypercubicLattice 2).Walk vr vl), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (phb_doubleDualShift p ∈ s(ur, vr) ∨ phb_doubleDualShift q ∈ s(ur, vr)) ∧ (phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' ∈ s(ul, vl)) ∧ (∀ z ∈ T.support, z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧ ∀ z ∈ T.support, z = vr ∨ z = vl ∨ z = phb_doubleDualShift q ∨ z = phb_doubleDualShift q' ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_directedSourceWalk_withProvenance hurv hulv

/--
[rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {ur vr ul vl : Site 2}
-- given
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (T : (hypercubicLattice 2).Walk vr vl), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ ∀ z ∈ T.support, z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk hurv hulv

/--
[rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_withSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_withSource_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {ur vr ul vl : Site 2}
-- given
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p') (T : (hypercubicLattice 2).Walk vr vl), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' omega) ∧ ∀ z ∈ T.support, z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨ ∃ a ∈ w.support, phb_doubleDualShift a = z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_withSource hurv hulv

/--
[rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_withEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_withEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {ur vr ul vl : Site 2}
-- given
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p') (T : (hypercubicLattice 2).Walk vr vl), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' omega) ∧ (∀ e ∈ w.edges, rlc_twoChannelFullAmbientConfig gamma gamma' omega e = true) ∧ (∀ a ∈ w.support, phb_doubleDualShift a ∈ T.support) ∧ (∀ e ∈ w.edges, Sym2.map phb_doubleDualShift e ∈ T.edges) ∧ (phb_doubleDualShift q ∈ s(ur, vr) → phb_doubleDualShift q ∈ T.support) ∧ (phb_doubleDualShift q' ∈ s(ul, vl) → phb_doubleDualShift q' ∈ T.support) ∧ (∀ z ∈ T.support, z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨ ∃ a ∈ w.support, phb_doubleDualShift a = z) ∧ ∀ e ∈ T.edges, (∀ z ∈ e, z = vr ∨ z = ur ∨ z = phb_doubleDualShift p) ∨ (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e) ∨ ∀ z ∈ e, z = vl ∨ z = ul ∨ z = phb_doubleDualShift p' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_directedReachableShiftWalk_withEdges hurv hulv

/--
[rlc_dualReflect_doubleDualShift_eq_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_dualReflect_doubleDualShift_eq_flipX_eq
  {z : Site 2} :
-- imply
  rlc_dualReflect (phb_doubleDualShift z) = rlc_flipX z := by
-- proof
  apply StatMech.Universality.rlc_dualReflect_doubleDualShift_eq_flipX z

/--
[rlc_faceFlipX_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_faceFlipX_involutive_eq
  {f : Site 2} :
-- imply
  rlc_faceFlipX (rlc_faceFlipX f) = f := by
-- proof
  apply StatMech.Universality.rlc_faceFlipX_involutive f

/--
[rlc_connectorFaceBox_faceFlipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_connectorFaceBox_faceFlipX_iff_eq
  {n : Int}
  {f : Site 2} :
-- imply
  f ∈ rlc_connectorFaceBox n ↔ rlc_faceFlipX f ∈ rlc_connectorFaceBox n := by
-- proof
  apply StatMech.Universality.rlc_connectorFaceBox_faceFlipX_iff n f

/--
[rlc_connectorFourTraceEdges_flipX_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_connectorFourTraceEdges_flipX_iff_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)} :
-- imply
  e ∈ rlc_connectorFourTraceEdges gamma gamma' ↔ Sym2.map rlc_flipX e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_connectorFourTraceEdges_flipX_iff gamma gamma' e

/--
[rlc_sharedPrimalEdge_faceFlipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_sharedPrimalEdge_faceFlipX_eq
  {f g : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g) :
-- imply
  sharedPrimalEdge (rlc_faceFlipX f) (rlc_faceFlipX g) = Sym2.map rlc_flipX (sharedPrimalEdge f g) := by
-- proof
  apply StatMech.Universality.rlc_sharedPrimalEdge_faceFlipX hfg

/--
[rlc_flankFaces_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_flankFaces_flipX_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  flankFaces (rlc_flipX a) (rlc_flipX b) = Sym2.map rlc_faceFlipX (flankFaces a b) := by
-- proof
  apply StatMech.Universality.rlc_flankFaces_flipX hab

/--
[RlcBookFaithfulTracePair.centralFaceRegion_faceFlipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma centralFaceRegion_faceFlipX_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hf : f ∈ rlc_connectorCentralFaceRegion gamma gamma') :
-- imply
  rlc_faceFlipX f ∈ rlc_connectorCentralFaceRegion gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.centralFaceRegion_faceFlipX hfaith hf

/--
[RlcBookFaithfulTracePair.centralFacePlanarEdges_flipX](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma centralFacePlanarEdges_flipX_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {a b : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hab : (hypercubicLattice 2).Adj a b)
  (he : s(a, b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma') :
-- imply
  s(rlc_flipX a, rlc_flipX b) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.centralFacePlanarEdges_flipX hfaith hab he

/--
[rlc_flipXEdge_target_or_originalTrace_or_notPlanar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_flipXEdge_target_or_originalTrace_or_notPlanar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  (∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s(rlc_flipX a, rlc_flipX b)) ∨ s(rlc_flipX a, rlc_flipX b) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨ s(rlc_flipX a, rlc_flipX b) ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_flipXEdge_target_or_originalTrace_or_notPlanar gamma gamma' hab

/--
[rlc_originalTraceEdge_not_crosses_liftVertexCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_originalTraceEdge_not_crosses_liftVertexCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {B : Set (RlcConnectorVertex n)}
  {a b : Site 2}
-- given
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (htrace : s(a, b) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  ¬rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(a, b) := by
-- proof
  apply StatMech.Universality.rlc_originalTraceEdge_not_crosses_liftVertexCut gamma gamma' B hBright hBleft htrace

/--
[rlc_twoChannelFullPhysical_noPair_rawTarget_sourceMissing_or_notAcrossA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_rawTarget_sourceMissing_or_notAcrossA_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) (target.1.map Subtype.val)) :
-- imply
  (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_rawTarget_sourceMissing_or_notAcrossA A B hnoPair target hcrossB

/--
[rlc_pimsEdgeEquiv_flipXEdge_sharedEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_flipXEdge_sharedEndpoint_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  ∃ z ∈ s(a, b), z ∈ rlc_pimsEdgeEquiv s(rlc_flipX a, rlc_flipX b) := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_flipXEdge_sharedEndpoint hab

/--
[rlc_latticeEdge_threeSupport_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_latticeEdge_threeSupport_cases_eq
  {x y a b c : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y)
  (hsupport : ∀ z ∈ s(x, y), z = a ∨ z = b ∨ z = c) :
-- imply
  s(x, y) = s(a, b) ∨ s(x, y) = s(a, c) ∨ s(x, y) = s(b, c) := by
-- proof
  apply StatMech.Universality.rlc_latticeEdge_threeSupport_cases hxy hsupport

/--
[rlc_doubleDualShift_eq_dualReflect_symm_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_doubleDualShift_eq_dualReflect_symm_iff_eq
  {p w : Site 2} :
-- imply
  phb_doubleDualShift p = rlc_dualReflect.symm w ↔ p = rlc_flipX w := by
-- proof
  apply StatMech.Universality.rlc_doubleDualShift_eq_dualReflect_symm_iff p w

/--
[rlc_shiftedReach_ne_dualReflectSymm_of_flippedLeftTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_shiftedReach_ne_dualReflectSymm_of_flippedLeftTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p w : Site 2}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hwLeft : rlc_flipX w ∈ rlc_pathVertices gamma'.1) :
-- imply
  phb_doubleDualShift p ≠ rlc_dualReflect.symm w := by
-- proof
  apply StatMech.Universality.rlc_shiftedReach_ne_dualReflectSymm_of_flippedLeftTrace hno hpReach hwLeft

/--
[rlc_shiftedExterior_ne_dualReflectSymm_of_flippedRightTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_shiftedExterior_ne_dualReflectSymm_of_flippedRightTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {q w : Site 2}
-- given
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hwRight : rlc_flipX w ∈ rlc_pathVertices gamma.1) :
-- imply
  phb_doubleDualShift q ≠ rlc_dualReflect.symm w := by
-- proof
  apply StatMech.Universality.rlc_shiftedExterior_ne_dualReflectSymm_of_flippedRightTrace hqOut hwRight

/--
[rlc_shiftedReach_ne_exclusiveReflectedLeftFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_shiftedReach_ne_exclusiveReflectedLeftFace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p f : Site 2}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hfLeft : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f)) :
-- imply
  phb_doubleDualShift p ≠ f := by
-- proof
  apply StatMech.Universality.rlc_shiftedReach_ne_exclusiveReflectedLeftFace hno hpReach hfLeft

/--
[rlc_shiftedExterior_ne_exclusiveReflectedRightFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_shiftedExterior_ne_exclusiveReflectedRightFace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {q f : Site 2}
-- given
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hfRight : RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect f)) :
-- imply
  phb_doubleDualShift q ≠ f := by
-- proof
  apply StatMech.Universality.rlc_shiftedExterior_ne_exclusiveReflectedRightFace hqOut hfRight

/--
[rlc_shiftedExterior_mem_or_adj_boundaryEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_shiftedExterior_mem_or_adj_boundaryEdge_eq
  {p q f g : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q)
  (hinc : phb_doubleDualShift p ∈ s(f, g) ∨ phb_doubleDualShift q ∈ s(f, g)) :
-- imply
  phb_doubleDualShift q ∈ s(f, g) ∨ ∃ t ∈ s(f, g), (hypercubicLattice 2).Adj (phb_doubleDualShift q) t := by
-- proof
  apply StatMech.Universality.rlc_shiftedExterior_mem_or_adj_boundaryEdge hpq hinc

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_tetheredShiftedWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_tetheredShiftedWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl A B : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (W : (hypercubicLattice 2).Walk A B), (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧ s(ur, vr) ≠ s(ul, vl) ∧ (RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' (rlc_dualReflect A) ∨ ∃ p : Site 2, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧ A = phb_doubleDualShift p) ∧ (RlcTwoChannelFullPhysicalLeftArcTargetBadLocation gamma gamma' (rlc_dualReflect B) ∨ ∃ p : Site 2, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p ∧ B = phb_doubleDualShift p) ∧ ∀ z ∈ W.support, z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_tetheredShiftedWalk hbad

/--
[rlc_twoChannelFullPhysical_noGood_rightLeftPrefixes_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noGood_rightLeftPrefixes_disjoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∀ z : Site 2, z ∈ qr.support → z ∈ ql.support → False := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noGood_rightLeftPrefixes_disjoint hnoGood hxPath hyPath qr ql

/--
[rlc_twoChannelFullPhysical_noGood_prefixEndpoints_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noGood_prefixEndpoints_not_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable ur ul := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noGood_prefixEndpoints_not_reachable hnoGood hxPath hyPath qr ql

/--
[rlc_twoChannelFullPhysical_reflectedLeftWalk_terminal_location](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftWalk_terminal_location_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hxOriginal : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect x ∈ rlc_pathVertices gamma'.1)
  (hleft : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (hloc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect u) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect u)) :
-- imply
  RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect u) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftWalk_terminal_location hfaith q hxOriginal hleft hloc

/--
[rlc_twoChannelFullPhysical_reflectedRightWalk_terminal_location](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedRightWalk_terminal_location_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hxOriginal : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect x ∈ rlc_pathVertices gamma'.1)
  (hright : ∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (hloc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect u) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect u)) :
-- imply
  RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect u) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedRightWalk_terminal_location hfaith q hxOriginal hright hloc

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_boundaryIncidenceOrientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_boundaryIncidenceOrientation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨ phb_doubleDualShift q ∈ s(ur, vr))
  (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' ∈ s(ul, vl)) :
-- imply
  (phb_doubleDualShift p = vr ∨ phb_doubleDualShift q ∈ s(ur, vr)) ∧ (phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' = vl) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_boundaryIncidenceOrientation hno hrow hpReach hqOut' hincR hincL

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceOrientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceOrientation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨ phb_doubleDualShift q ∈ s(ur, vr))
  (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' ∈ s(ul, vl)) :
-- imply
  (phb_doubleDualShift p = vr ∨ phb_doubleDualShift q ∈ s(ur, vr)) ∧ (phb_doubleDualShift p' = vl ∨ phb_doubleDualShift q' ∈ s(ul, vl)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceOrientation hno hrow hpReach hpReach' hincR hincL

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceEndpointCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceEndpointCases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨ phb_doubleDualShift q ∈ s(ur, vr))
  (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' ∈ s(ul, vl)) :
-- imply
  (phb_doubleDualShift p = vr ∨ phb_doubleDualShift q = ur ∨ phb_doubleDualShift q = vr) ∧ (phb_doubleDualShift p' = vl ∨ phb_doubleDualShift q' = ul ∨ phb_doubleDualShift q' = vl) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_boundaryIncidenceEndpointCases hno hrow hpReach hpReach' hincR hincL

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_reachableIncidence_or_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_reachableIncidence_or_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨ phb_doubleDualShift q ∈ s(ur, vr))
  (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' ∈ s(ul, vl)) :
-- imply
  (phb_doubleDualShift p = vr ∧ phb_doubleDualShift p' = vl) ∨ phb_doubleDualShift q ∈ s(ur, vr) ∨ phb_doubleDualShift q' ∈ s(ul, vl) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_reachableIncidence_or_exterior hno hrow hpReach hpReach' hincR hincL

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_boundaryIncidenceEndpointCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_boundaryIncidenceEndpointCases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨ phb_doubleDualShift q ∈ s(ur, vr))
  (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' ∈ s(ul, vl)) :
-- imply
  (phb_doubleDualShift p = vr ∨ phb_doubleDualShift q = ur ∨ phb_doubleDualShift q = vr) ∧ (phb_doubleDualShift p' = ul ∨ phb_doubleDualShift p' = vl ∨ phb_doubleDualShift q' = vl) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_boundaryIncidenceEndpointCases hno hrow hpReach hqOut' hincR hincL

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_droppedEndpointGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_droppedEndpointGeometry_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  ((vr = ![ur 0 + 1, ur 1] ∧ phb_doubleDualShift p = ![ur 0, ur 1 - 1] ∧ phb_doubleDualShift q = ur) ∨ (vr = ![ur 0 - 1, ur 1] ∧ ((phb_doubleDualShift p = vr ∧ phb_doubleDualShift q = ![ur 0 - 1, ur 1 - 1]) ∨ (phb_doubleDualShift p = ![ur 0 - 1, ur 1 - 1] ∧ phb_doubleDualShift q = vr))) ∨ (vr = ![ur 0, ur 1 + 1] ∧ phb_doubleDualShift p = ![ur 0 - 1, ur 1] ∧ phb_doubleDualShift q = ur) ∨ (vr = ![ur 0, ur 1 - 1] ∧ ((phb_doubleDualShift p = vr ∧ phb_doubleDualShift q = ![ur 0 - 1, ur 1 - 1]) ∨ (phb_doubleDualShift p = ![ur 0 - 1, ur 1 - 1] ∧ phb_doubleDualShift q = vr)))) ∧ ((vl = ![ul 0 + 1, ul 1] ∧ phb_doubleDualShift p' = ul ∧ phb_doubleDualShift q' = ![ul 0, ul 1 - 1]) ∨ (vl = ![ul 0 - 1, ul 1] ∧ ((phb_doubleDualShift p' = vl ∧ phb_doubleDualShift q' = ![ul 0 - 1, ul 1 - 1]) ∨ (phb_doubleDualShift p' = ![ul 0 - 1, ul 1 - 1] ∧ phb_doubleDualShift q' = vl))) ∨ (vl = ![ul 0, ul 1 + 1] ∧ phb_doubleDualShift p' = ul ∧ phb_doubleDualShift q' = ![ul 0 - 1, ul 1]) ∨ (vl = ![ul 0, ul 1 - 1] ∧ ((phb_doubleDualShift p' = vl ∧ phb_doubleDualShift q' = ![ul 0 - 1, ul 1 - 1]) ∨ (phb_doubleDualShift p' = ![ul 0 - 1, ul 1 - 1] ∧ phb_doubleDualShift q' = vl)))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_droppedEndpointGeometry hno hrow hurv hulv hpq hpq' hpReach hqOut'

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  phb_doubleDualShift p = vr ∨ p = ur ∨ p = vr := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cases hno hrow hurv hulv hpq hpq' hpReach hqOut'

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_exact_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_exact_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  (phb_doubleDualShift p = vr ∧ q = ur) ∨ (p = ur ∧ phb_doubleDualShift q = vr) ∨ (p = vr ∧ phb_doubleDualShift q = ur) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_exact_cases hno hrow hurv hulv hpq hpq' hpReach hqOut'

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_shiftedExteriorAtUr_mem_leftTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_shiftedExteriorAtUr_mem_leftTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur ul q : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hqShift : phb_doubleDualShift q = ur) :
-- imply
  q ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_shiftedExteriorAtUr_mem_leftTrace hrow hqShift

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_exteriorNeighbour_of_p_eq_ur](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_exteriorNeighbour_of_p_eq_ur_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hpUr : p = ur) :
-- imply
  ∃ w ∈ rlc_pathVertices gamma'.1, q = ![w 0 - 1, w 1] ∨ q = ![w 0, w 1 - 1] := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_exteriorNeighbour_of_p_eq_ur hno hrow hurv hulv hpq hpq' hpReach hqOut' hpUr

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_ur_sourceCarrier_or_location](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_ur_sourceCarrier_or_location_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul p q : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpUr : p = ur) :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∨ (p 0 = -2 * n ∨ p 0 = 2 * n ∨ p 1 = -n ∨ p 1 = n) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_ur_sourceCarrier_or_location hno hrow hurv hpq hpqAdj hpReach hpUr

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_q_eq_ur_sourceCarrier_or_location](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_q_eq_ur_sourceCarrier_or_location_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul p q : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqUr : q = ur) :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∨ (p 0 = -2 * n ∨ p 0 = 2 * n ∨ p 1 = -n ∨ p 1 = n) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_q_eq_ur_sourceCarrier_or_location hno hrow hurv hpq hpqAdj hpReach hqUr

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceEdge_traceGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceEdge_traceGap_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hpVr : p = vr) :
-- imply
  ∃ w ∈ rlc_pathVertices gamma'.1, q = w ∧ ((sharedPrimalEdge ur vr = s((![w 0, w 1 - 1] : Site 2), w) ∧ s((![w 0, w 1 - 1] : Site 2), w) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∨ (sharedPrimalEdge ur vr = s((![w 0 - 1, w 1] : Site 2), w) ∧ s((![w 0 - 1, w 1] : Site 2), w) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceEdge_traceGap hno hrow hurv hulv hpq hpq' hpReach hqOut' hpVr

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_location](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_location_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hpVr : p = vr) :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∨ (p 0 = -2 * n ∨ p 0 = 2 * n ∨ p 1 = -n ∨ p 1 = n) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_location hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceCarrier_or_location](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceCarrier_or_location_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∨ (p 0 = -2 * n ∨ p 0 = 2 * n ∨ p 1 = -n ∨ p 1 = n) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceCarrier_or_location hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut'

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_nonwall_location](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_nonwall_location_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hn : 0 < n)
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hpVr : p = vr) :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∨ p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧ sharedPrimalEdge ur vr ∉ rlc_connectorFourTraceEdges gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCarrier_or_nonwall_location hn hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourcePrefix_capstone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourcePrefix_capstone_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hn : 0 < n)
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hpVr : p = vr) :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ (p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∨ ∃ z : Site 2, RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ sharedPrimalEdge ur vr ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧ (s(p, z) ∈ rlc_connectorFourTraceEdges gamma gamma' ∨ (z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourcePrefix_capstone hn hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceTraceCross_capstone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceTraceCross_capstone_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hn : 0 < n)
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hpVr : p = vr) :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ (p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∨ ∃ z : Site 2, RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ sharedPrimalEdge ur vr ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧ (s(p, z) ∈ rlc_reflectedPathEdges gamma.1 ∨ (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧ ∀ y : Site 2, (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q → s(p, y) ∈ rlc_reflectedPathEdges gamma.1)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceTraceCross_capstone hn hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCoordinate_capstone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCoordinate_capstone_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hn : 0 < n)
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hpVr : p = vr) :
-- imply
  RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ (p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∨ ∃ z : Site 2, RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ sharedPrimalEdge ur vr ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧ ((∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, z)) ∨ (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧ ∀ y : Site 2, (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q → ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, y))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_p_eq_vr_sourceCoordinate_capstone hn hno hrow hurv hulv hpq hpq' hpqAdj hpReach hqOut' hpVr

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cycleContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cycleContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' u : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hurC : ur ∈ c.support)
  (hvrC : vr ∈ c.support) :
-- imply
  phb_doubleDualShift p ∈ c.support ∨ p ∈ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_cycleContact hno hrow hurv hulv hpq hpq' hpReach hqOut' c hurC hvrC

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_noncarrierEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_noncarrierEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ur vr)
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr)) :
-- imply
  (∃ w : Site 2, (hypercubicLattice 2).Adj (phb_doubleDualShift p) w ∧ s(phb_doubleDualShift p, w) ∈ (rlc_orderedContourArc c hx hy).edges ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' (phb_doubleDualShift p) w) ∨ ∃ w : Site 2, (hypercubicLattice 2).Adj p w ∧ s(p, w) ∈ (rlc_orderedContourArc c hx hy).edges ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' p w := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_rightDroppedEndpoint_noncarrierEdge hno hrow hurv hulv hpq hpq' hpReach hqOut' hbad hdecR

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  phb_doubleDualShift p' = ul ∨ phb_doubleDualShift p' = vl ∨ p' = ul := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_cases hno hrow hurv hulv hpq hpq' hpReach hqOut'

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_noncarrierEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_noncarrierEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ul vl)
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl)) :
-- imply
  (∃ w : Site 2, (hypercubicLattice 2).Adj (phb_doubleDualShift p') w ∧ s(phb_doubleDualShift p', w) ∈ (rlc_complementaryContourArc c hx hy).edges ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' (phb_doubleDualShift p') w) ∨ ∃ w : Site 2, (hypercubicLattice 2).Adj p' w ∧ s(p', w) ∈ (rlc_complementaryContourArc c hx hy).edges ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' p' w := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_leftDroppedEndpoint_noncarrierEdge hno hrow hurv hulv hpq hpq' hpReach hqOut' hbad hdecL

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_twoDroppedEndpoint_noncarrierEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_twoDroppedEndpoint_noncarrierEdges_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hbadR : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ur vr)
  (hbadL : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ul vl)
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr))
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl)) :
-- imply
  ((∃ w : Site 2, (hypercubicLattice 2).Adj (phb_doubleDualShift p) w ∧ s(phb_doubleDualShift p, w) ∈ (rlc_orderedContourArc c hx hy).edges ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' (phb_doubleDualShift p) w) ∨ ∃ w : Site 2, (hypercubicLattice 2).Adj p w ∧ s(p, w) ∈ (rlc_orderedContourArc c hx hy).edges ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' p w) ∧ ((∃ w : Site 2, (hypercubicLattice 2).Adj (phb_doubleDualShift p') w ∧ s(phb_doubleDualShift p', w) ∈ (rlc_complementaryContourArc c hx hy).edges ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' (phb_doubleDualShift p') w) ∨ ∃ w : Site 2, (hypercubicLattice 2).Adj p' w ∧ s(p', w) ∈ (rlc_complementaryContourArc c hx hy).edges ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' p' w) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_twoDroppedEndpoint_noncarrierEdges hno hrow hurv hulv hpq hpq' hpReach hqOut' hbadR hbadL hdecR hdecL

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_incidentFaces_axisSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_incidentFaces_axisSides_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl) :
-- imply
  vr 0 ≤ -1 ∧ -1 ≤ vl 0 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_incidentFaces_axisSides hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceEndpoints_axisSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceEndpoints_axisSides_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q')) :
-- imply
  p 0 < 0 ∧ 0 ≤ p' 0 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceEndpoints_axisSides hrow hurv hulv hpq hpq'

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_meets_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_meets_axis_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl) :
-- imply
  ∃ a ∈ T.support, a 0 = -1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_meets_axis hrow hurv hulv T

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_axisProvenance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_axisProvenance_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) :
-- imply
  ∃ v ∈ T.support, v 0 = -1 ∧ (v = vr ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, a 0 = 0 ∧ phb_doubleDualShift a = v) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_transverseWalk_axisProvenance hrow hurv hulv T hTprov

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisSourceSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisSourceSplice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (T : (hypercubicLattice 2).Walk vr vl), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) ∧ ∃ v ∈ T.support, v 0 = -1 ∧ (v = vr ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, a 0 = 0 ∧ phb_doubleDualShift a = v) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisSourceSplice hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_wallFamilyRowThree_incidentFaces_axisSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowThree_incidentFaces_axisSides_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl) :
-- imply
  vl 0 ≤ -1 ∧ -1 ≤ vr 0 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowThree_incidentFaces_axisSides hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_wallFamilyRowThree_sourceEndpoints_axisSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowThree_sourceEndpoints_axisSides_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q')) :
-- imply
  0 ≤ p 0 ∧ p' 0 < 0 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowThree_sourceEndpoints_axisSides hrow hurv hulv hpq hpq'

/--
[rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_meets_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_meets_axis_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl) :
-- imply
  ∃ a ∈ T.support, a 0 = -1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_meets_axis hrow hurv hulv T

/--
[rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_axisProvenance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_axisProvenance_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) :
-- imply
  ∃ v ∈ T.support, v 0 = -1 ∧ (v = vr ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, a 0 = 0 ∧ phb_doubleDualShift a = v) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowThree_transverseWalk_axisProvenance hrow hurv hulv T hTprov

/--
[rlc_twoChannelFullPhysical_wallFamilyRowThree_axisSourceSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowThree_axisSourceSplice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (T : (hypercubicLattice 2).Walk vr vl), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) ∧ ∃ v ∈ T.support, v 0 = -1 ∧ (v = vr ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, a 0 = 0 ∧ phb_doubleDualShift a = v) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowThree_axisSourceSplice hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_wallTerminalFamilyTable_iff_rows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallTerminalFamilyTable_iff_rows_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul} :
-- imply
  RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable gamma gamma' omega qr ql ↔ RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql ∨ RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql ∨ RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree gamma gamma' omega qr ql ∨ RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour gamma gamma' omega qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallTerminalFamilyTable_iff_rows qr ql

/--
[rlc_twoChannelFullPhysical_twoArcWallTerminalFamilyTable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcWallTerminalFamilyTable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hallR : ∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hallL : ∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma')
  (hurLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ur) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ur))
  (hulLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ul) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ul)) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable gamma gamma' omega qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcWallTerminalFamilyTable hfaith qr ql hxPath hyPath hallR hallL hurLoc hulLoc

/--
[rlc_twoChannelFullPhysical_sameReflectedLeft_end_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sameReflectedLeft_end_order_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hqrLeft : ∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (hqlLeft : ∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (hurLeft : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ur))
  (hulLeft : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ul)) :
-- imply
  let W := (rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom W.support.idxOf (rlc_dualReflect ur) < W.support.idxOf (rlc_dualReflect ul) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sameReflectedLeft_end_order hnoGood z hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hqrLeft hqlLeft hurLeft hulLeft

/--
[rlc_twoChannelFullPhysical_sameReflectedRight_end_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sameReflectedRight_end_order_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hrRight : r ∈ rlc_pathVertices gamma.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxAxis : rlc_dualReflect x = (gamma.1.1 : Site 2))
  (hyr : rlc_dualReflect y = rlc_flipX r)
  (hqrRight : ∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (hqlRight : ∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (hurRight : RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ur))
  (hulRight : RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ul)) :
-- imply
  let W := ((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse W.support.idxOf (rlc_dualReflect ul) < W.support.idxOf (rlc_dualReflect ur) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sameReflectedRight_end_order hnoGood hrRight hxPath hyPath qr ql hxAxis hyr hqrRight hqlRight hurRight hulRight

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ T : (hypercubicLattice 2).Walk vr vl, (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) ∧ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice hnoGood hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_wallFamilyRowFour_orderedSourceSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowFour_orderedSourceSplice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hrRight : r ∈ rlc_pathVertices gamma.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxAxis : rlc_dualReflect x = (gamma.1.1 : Site 2))
  (hyr : rlc_dualReflect y = rlc_flipX r)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ T : (hypercubicLattice 2).Walk vr vl, (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) ∧ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support.idxOf (rlc_dualReflect ul) < (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support.idxOf (rlc_dualReflect ur) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowFour_orderedSourceSplice hnoGood hrRight hxPath hyPath qr ql hxAxis hyr hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_twoArcWallFamily_orderedOutcome](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcWallFamily_orderedOutcome_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hurLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ur) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ur))
  (hulLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ul) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ul))
  (h : RlcTwoChannelFullPhysicalTwoArcWallFamilyTruthTable gamma gamma' omega flipLeft qr ql) :
-- imply
  RlcTwoChannelFullPhysicalOrderedWallFamilyOutcome gamma gamma' omega flipLeft qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcWallFamily_orderedOutcome hfaith hnoGood hzRight hzLeft hxPath hyPath flipLeft qr ql hurLoc hulLoc h

/--
[rlc_twoChannelFullPhysical_exactOrderedWallTerminalRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_exactOrderedWallTerminalRows_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hfirst : ∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
  (htable : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable gamma gamma' omega qr ql) :
-- imply
  RlcTwoChannelFullPhysicalExactOrderedWallTerminalRows gamma gamma' omega flipLeft qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_exactOrderedWallTerminalRows hfaith hnoGood right flipLeft hzRight hzLeft hxPath hyPath hxOrder hyOrder hfirst qr ql htable

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateOrderCases gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket_cases h

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  (rlc_dualReflect x = z ∧ rlc_dualReflect y = rlc_flipX z) ∨ (∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q < (rlc_ambientCrossingWalk gamma.1).support.idxOf z) ∨ ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition hzCandidate hyPath hflipLeftRank h

/--
[rlc_rightAmbientTrace_segment_of_idxOf_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_rightAmbientTrace_segment_of_idxOf_le_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {a b : Site 2}
-- given
  (haPath : a ∈ rlc_pathVertices gamma.1)
  (hbPath : b ∈ rlc_pathVertices gamma.1)
  (hab : (rlc_ambientCrossingWalk gamma.1).support.idxOf a ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf b) :
-- imply
  ∃ P : (hypercubicLattice 2).Walk a b, ∀ v ∈ P.support, v ∈ (rlc_ambientCrossingWalk gamma.1).support := by
-- proof
  apply StatMech.Universality.rlc_rightAmbientTrace_segment_of_idxOf_le haPath hbPath hab

/--
[rlc_rightAmbientTrace_prefix_meets_segment_only_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_rightAmbientTrace_prefix_meets_segment_only_start_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {a b v : Site 2}
-- given
  (haPath : a ∈ rlc_pathVertices gamma.1)
  (hbPath : b ∈ rlc_pathVertices gamma.1)
  (hab : (rlc_ambientCrossingWalk gamma.1).support.idxOf a ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf b)
  (hvPrefix : v ∈ ((rlc_ambientCrossingWalk gamma.1).takeUntil a ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 a).2 haPath)).support)
  (hvSegment : v ∈ (((rlc_ambientCrossingWalk gamma.1).dropUntil a ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 a).2 haPath)).takeUntil b ((rlc_isPath_mem_dropUntil_iff_idxOf_le (rlc_ambientCrossingWalk gamma.1) (rlc_ambientCrossingWalk_isPath gamma.1) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 a).2 haPath) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 b).2 hbPath)).2 hab)).support) :
-- imply
  v = a := by
-- proof
  apply StatMech.Universality.rlc_rightAmbientTrace_prefix_meets_segment_only_start haPath hbPath hab hvPrefix hvSegment

/--
[RlcBookFaithfulTracePair.dualSymm_images_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma dualSymm_images_ne_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r l : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hl : l ∈ rlc_pathVertices gamma'.1) :
-- imply
  rlc_dualReflect.symm r ≠ rlc_dualReflect.symm l := by
-- proof
  apply StatMech.Universality.RlcBookFaithfulTracePair.dualSymm_images_ne hfaith hr hl

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_earlierTraceSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_earlierTraceSegment_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x : Site 2}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierContact gamma gamma' z x) :
-- imply
  RlcTwoChannelFullPhysicalWallFamilyRowTwoEarlierTraceSegment gamma gamma' z x := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_earlierTraceSegment hzCandidate h

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_laterTraceSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_laterTraceSegment_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterContact gamma gamma' (z := z) (y := y) flipLeft) :
-- imply
  RlcTwoChannelFullPhysicalWallFamilyRowTwoLaterTraceSegment gamma gamma' (z := z) (y := y) flipLeft := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_laterTraceSegment hzCandidate h

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_traceSegmentCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_traceSegmentCases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateOrderCases gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceSegmentCases gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_traceSegmentCases hzCandidate h

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_traceBracketWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_traceBracketWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceSegmentCases gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_traceBracketWalk hzCandidate h

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_physicalTraceBracketWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_physicalTraceBracketWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  ∃ Q : (hypercubicLattice 2).Walk x y, rlc_dualReflect.symm z ∈ Q.support ∧ ∀ v ∈ Q.support, v ∈ rect (-2 * n - 4) (2 * n + 2) (-n - 4) (n + 2) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_physicalTraceBracketWalk h

/--
[rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hv : v ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  v ∈ rect (-2 * n - 1) (2 * n) (-n - 1) n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_filledBoundarySupport_mem_faceBox hn gamma gamma' omega hv

/--
[rlc_twoChannelFullPhysical_innerTraceSourceSpliceWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_innerTraceSourceSpliceWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hTBox : ∀ v ∈ T.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) :
-- imply
  ∃ V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2)), (∀ v ∈ V.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧ (((rlc_ambientCrossingWalk gamma.1).takeUntil (rlc_dualReflect x) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 (rlc_dualReflect x)).2 hxPath)).map rlc_dualReflectSymmLatticeHom).support ⊆ V.support ∧ (((rlc_ambientCrossingWalk gamma'.1).dropUntil (rlc_dualReflect y) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_dualReflect y)).2 hyPath)).map rlc_dualReflectSymmLatticeHom).support ⊆ V.support ∧ qr.support ⊆ V.support ∧ ql.support ⊆ V.support ∧ T.support ⊆ V.support ∧ (∀ v ∈ V.support, v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil (rlc_dualReflect x) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 (rlc_dualReflect x)).2 hxPath)).map rlc_dualReflectSymmLatticeHom).support ∨ v ∈ qr.support ∨ v = ur ∨ v = vr ∨ v ∈ T.support ∨ v = vl ∨ v = ul ∨ v ∈ ql.support ∨ v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil (rlc_dualReflect y) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_dualReflect y)).2 hyPath)).map rlc_dualReflectSymmLatticeHom).support) ∧ ∀ e ∈ V.edges, e ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil (rlc_dualReflect x) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 (rlc_dualReflect x)).2 hxPath)).map rlc_dualReflectSymmLatticeHom).edges ∨ e ∈ qr.edges ∨ e = s(ur, vr) ∨ e ∈ T.edges ∨ e = s(ul, vl) ∨ e ∈ ql.edges ∨ e ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil (rlc_dualReflect y) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_dualReflect y)).2 hyPath)).map rlc_dualReflectSymmLatticeHom).edges := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_innerTraceSourceSpliceWalk hfaith qr ql T hurv hulv hxPath hyPath hTBox

/--
[rlc_twoChannelFullPhysical_sourceSplice_BChanging_terminal_or_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceSplice_BChanging_terminal_or_bridge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hTBox : ∀ v ∈ T.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) :
-- imply
  ∃ (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2), s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ (s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨ s(f, g) = s(ul, vl)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceSplice_BChanging_terminal_or_bridge hfaith A B hAright hAleft hBright hBleft hnoPair qr ql T hurv hulv hxPath hyPath hTBox

/--
[rlc_twoChannelFullPhysical_reachableShiftSplice_mem_broadBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachableShiftSplice_mem_broadBox_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {ur vr ul vl : Site 2}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hn : 0 < n)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) :
-- imply
  ∀ v ∈ T.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachableShiftSplice_mem_broadBox hn hurv hulv T hTprov

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedBChangingSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedBChangingSplice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {z x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl) :
-- imply
  ∃ (T : (hypercubicLattice 2).Walk vr vl) (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2), (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A), phb_doubleDualShift a = v) ∧ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ (s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨ s(f, g) = s(ul, vl)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedBChangingSplice hn hfaith A B hAright hAleft hBright hBleft hnoPair hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_terminalFailure_or_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_terminalFailure_or_bridge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
  {T : (hypercubicLattice 2).Walk vr vl}
  {f g : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g))
  (hlocation : s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨ s(f, g) = s(ul, vl)) :
-- imply
  s(f, g) ∈ T.edges ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure gamma gamma' B ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalExclusiveReflectedLeftTerminalFailure gamma gamma' B ul vl) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_terminalFailure_or_bridge A B hAright hAleft hnoPair qr ql hrow hurv hulv hcross hlocation

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactTerminalResidue_or_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactTerminalResidue_or_bridge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
  {T : (hypercubicLattice 2).Walk vr vl}
  {f g : Site 2}
-- given
  (hn : 0 < n)
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g))
  (hlocation : s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨ s(f, g) = s(ul, vl)) :
-- imply
  s(f, g) ∈ T.edges ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ul vl) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactTerminalResidue_or_bridge hn A B hAright hAleft hnoPair qr ql hrow hurv hulv hcross hlocation

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowFour_orderedBChangingSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowFour_orderedBChangingSplice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {r x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hrRight : r ∈ rlc_pathVertices gamma.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxAxis : rlc_dualReflect x = (gamma.1.1 : Site 2))
  (hyr : rlc_dualReflect y = rlc_flipX r)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl) :
-- imply
  ∃ (T : (hypercubicLattice 2).Walk vr vl) (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2), (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A), phb_doubleDualShift a = v) ∧ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support.idxOf (rlc_dualReflect ul) < (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support.idxOf (rlc_dualReflect ur) ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ (s(f, g) = s(ur, vr) ∨ s(f, g) ∈ T.edges ∨ s(f, g) = s(ul, vl)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowFour_orderedBChangingSplice hn hfaith A B hAright hAleft hBright hBleft hnoPair hrRight hxPath hyPath qr ql hxAxis hyr hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_noPair_sourceSplice_BChanging_exactSourceEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_sourceSplice_BChanging_exactSourceEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p') (T : (hypercubicLattice 2).Walk vr vl) (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ (∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) ∧ (∀ a ∈ w.support, phb_doubleDualShift a ∈ T.support) ∧ (∀ e ∈ w.edges, Sym2.map phb_doubleDualShift e ∈ T.edges) ∧ (∀ z ∈ T.support, z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨ ∃ a ∈ w.support, phb_doubleDualShift a = z) ∧ (∀ e ∈ T.edges, (∀ z ∈ e, z = vr ∨ z = ur ∨ z = phb_doubleDualShift p) ∨ (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e) ∨ ∀ z ∈ e, z = vl ∨ z = ul ∨ z = phb_doubleDualShift p') ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ RlcTwoChannelFullPhysicalExactSourceSpliceEdgeResidue gamma gamma' A B ur vr ul vl w f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_sourceSplice_BChanging_exactSourceEdge hn hfaith A B hAright hAleft hBright hBleft hnoPair qr ql hurv hulv hxPath hyPath

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactSourceSpliceResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactSourceSpliceResidue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {x y ur vr ul vl p p' f g : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
  {w : (hypercubicLattice 2).Walk p p'}
-- given
  (hn : 0 < n)
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g))
  (hres : RlcTwoChannelFullPhysicalExactSourceSpliceEdgeResidue gamma gamma' A B ur vr ul vl w f g) :
-- imply
  RlcTwoChannelFullPhysicalRowOneExactSourceSpliceEdgeResidue gamma gamma' A B ur vr ul vl w f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_exactSourceSpliceResidue hn A B hAright hAleft hnoPair hrow hurv hulv w hcross hres

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {z x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p') (T : (hypercubicLattice 2).Walk vr vl) (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ (∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) ∧ (∀ a ∈ w.support, phb_doubleDualShift a ∈ T.support) ∧ (∀ e ∈ w.edges, Sym2.map phb_doubleDualShift e ∈ T.edges) ∧ (∀ a ∈ T.support, a = vr ∨ a = ur ∨ a = ul ∨ a = vl ∨ ∃ b ∈ w.support, phb_doubleDualShift b = a) ∧ (∀ e ∈ T.edges, (∀ a ∈ e, a = vr ∨ a = ur ∨ a = phb_doubleDualShift p) ∨ (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e) ∨ ∀ a ∈ e, a = vl ∨ a = ul ∨ a = phb_doubleDualShift p') ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧ RlcTwoChannelFullPhysicalRowOneExactSourceSpliceEdgeResidue gamma gamma' A B ur vr ul vl w f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice hn hfaith A B hAright hAleft hBright hBleft hnoPair hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hqrLeft : ∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (hqlRight : ∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (hurLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ur) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ur))
  (hulLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ul) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ul)) :
-- imply
  RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateBracket hfaith right flipLeft qr ql hzCandidate hxPath hyPath hxOrder hyOrder hrightPrefix hflipLeftRank hqrLeft hqlRight hurLoc hulLoc

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_minCandidate_bracket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_minCandidate_bracket_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzMin : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf q)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql) :
-- imply
  rlc_dualReflect x = z ∧ RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_minCandidate_bracket hfaith right flipLeft qr ql hzCandidate hzMin hxPath hyPath hxOrder hyOrder hrightPrefix hflipLeftRank hrow

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_maxCandidate_bracket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_maxCandidate_bracket_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzMax : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql) :
-- imply
  rlc_dualReflect y = rlc_flipX z ∧ RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket gamma gamma' (z := z) (x := x) (y := y) flipLeft := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_maxCandidate_bracket hfaith right flipLeft qr ql hzCandidate hzMax hxPath hyPath hxOrder hyOrder hrightPrefix hflipLeftRank hrow

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateProgress](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateProgress_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hqrLeft : ∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hqlRight : ∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (hulLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ul) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ul)) :
-- imply
  (∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) ∧ rlc_dualReflect x = z ∧ (∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∧ ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect y = rlc_flipX r ∧ r ∈ flipLeft.support ∧ (r = z ∨ (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf r) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateProgress hfaith flipLeft qr ql hzCandidate hyPath hyOrder hflipLeftRank hqrLeft hxz hqlRight hulLoc

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_maxCandidate_contacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_maxCandidate_contacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y u ur ul : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzMax : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hqrLeft : ∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hqlRight : ∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1)
  (hulLoc : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ul) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' (rlc_dualReflect ul)) :
-- imply
  (∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) ∧ rlc_dualReflect x = z ∧ (∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∧ rlc_dualReflect y = rlc_flipX z ∧ (((x ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧ x ∈ (rlc_orderedContourArc c hx hy).support) ∧ (y ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧ y ∈ (rlc_orderedContourArc c hx hy).support)) ∧ x ≠ y) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_maxCandidate_contacts hfaith c hx hy flipLeft qr ql hzRight hzLeft hzCandidate hzMax hyPath hyOrder hflipLeftRank hqrLeft hxz hqlRight hulLoc

/--
[rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable_factor_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (h : RlcTwoChannelFullPhysicalTwoArcWallFamilyTruthTable gamma gamma' omega flipLeft qr ql) :
-- imply
  (((∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) ∧ rlc_dualReflect x = z) ∨ ((∀ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∧ rlc_dualReflect x = (gamma.1.1 : Site 2))) ∧ (((∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma'.1) ∧ rlc_dualReflect y = (gamma'.1.2.1 : Site 2)) ∨ ((∀ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∈ rlc_reflectedPathEdges gamma.1) ∧ ∃ r ∈ rlc_pathVertices gamma.1, rlc_dualReflect y = rlc_flipX r ∧ r ∈ flipLeft.support)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcWallFamilyTruthTable_factor flipLeft qr ql h

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallOrientationCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallOrientationCases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y u : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hfirst : ∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (W : (hypercubicLattice 2).Walk ur ul), (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧ s(ur, vr) ≠ s(ul, vl) ∧ (∀ v ∈ W.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧ RlcTwoChannelFullPhysicalTetheredWallOrientationAlternative gamma gamma' omega flipLeft qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallOrientationCases hfaith right flipLeft hxPath hyPath hxOrder hyOrder hfirst hbad

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_tetheredOrderedWallCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_tetheredOrderedWallCases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y u : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hfirst : ∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (W : (hypercubicLattice 2).Walk ur ul), (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr ∧ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl ∧ s(ur, vr) ≠ s(ul, vl) ∧ (∀ v ∈ W.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧ RlcTwoChannelFullPhysicalTetheredOrderedWallOrientationAlternative gamma gamma' omega flipLeft qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_tetheredOrderedWallCases hfaith hnoGood right flipLeft hzRight hzLeft hxPath hyPath hxOrder hyOrder hfirst hbad

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_tetheredOrderedWallCases_withDirections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_tetheredOrderedWallCases_withDirections_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y u : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hfirst : ∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x) (W : (hypercubicLattice 2).Walk ur ul) (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr) (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl), rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr) ∧ (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl) ∧ s(ur, vr) ≠ s(ul, vl) ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ur vr ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ul vl ∧ RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr ∧ RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl ∧ (∀ v ∈ W.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧ RlcTwoChannelFullPhysicalTetheredOrderedWallOrientationAlternative gamma gamma' omega flipLeft qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_tetheredOrderedWallCases_withDirections hfaith hnoGood right flipLeft hzRight hzLeft hxPath hyPath hxOrder hyOrder hfirst hbad

/--
[rlc_prefix_not_all_fourTrace_iff_exists_nonWallEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_prefix_not_all_fourTrace_iff_exists_nonWallEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u} :
-- imply
  (¬∀ e ∈ q.edges, Sym2.map rlc_dualReflect e ∈ rlc_connectorFourTraceEdges gamma gamma') ↔ ∃ e ∈ q.edges, Sym2.map rlc_dualReflect e ∉ rlc_connectorFourTraceEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_prefix_not_all_fourTrace_iff_exists_nonWallEdge q

/--
[rlc_twoChannelFullPhysical_rightNonWallPrefix_staticCutReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rightNonWallPrefix_staticCutReach_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {x u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x u}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hbranch : ∃ e ∈ q.edges, Sym2.map rlc_dualReflect e ∉ rlc_connectorFourTraceEdges gamma gamma') :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ q.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ rlc_connectorOnRight gamma (rlc_twoChannelFullPhysicalLiftFace gamma x) ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable (rlc_twoChannelFullPhysicalLiftFace gamma x) (rlc_twoChannelFullPhysicalLiftFace gamma f) ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Adj (rlc_twoChannelFullPhysicalLiftFace gamma f) (rlc_twoChannelFullPhysicalLiftFace gamma g) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rightNonWallPrefix_staticCutReach gamma gamma' A hAright hAleft q hxPath hbranch

/--
[rlc_twoChannelFullPhysical_leftNonWallPrefix_staticCutReach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_leftNonWallPrefix_staticCutReach_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {y u : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y u}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hbranch : ∃ e ∈ q.edges, Sym2.map rlc_dualReflect e ∉ rlc_connectorFourTraceEdges gamma gamma') :
-- imply
  ∃ f g : Site 2, s(f, g) ∈ q.edges ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ rlc_connectorOnLeft gamma' (rlc_twoChannelFullPhysicalLiftFace gamma y) ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable (rlc_twoChannelFullPhysicalLiftFace gamma y) (rlc_twoChannelFullPhysicalLiftFace gamma f) ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Adj (rlc_twoChannelFullPhysicalLiftFace gamma f) (rlc_twoChannelFullPhysicalLiftFace gamma g) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_leftNonWallPrefix_staticCutReach gamma gamma' A hAright hAleft q hyPath hbranch

/--
[rlc_twoChannelFullPhysical_rightNonExclusiveLocalizedBad_atCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rightNonExclusiveLocalizedBad_atCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u v : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hbad : RlcTwoChannelFullPhysicalRightArcNonExclusiveLocalizedBad gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) u v) :
-- imply
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧ (rlc_dualReflect u ∈ rlc_pathVertices gamma.1 ∨ (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n)) ∨ ∃ p q : Site 2, sharedPrimalEdge u v = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullPhysicalLiftVertexCut A ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rightNonExclusiveLocalizedBad_atCut gamma gamma' A hAright hAleft hbad

/--
[rlc_twoChannelFullPhysical_leftNonExclusiveLocalizedBad_atCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_leftNonExclusiveLocalizedBad_atCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u v : Site 2}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hbad : RlcTwoChannelFullPhysicalLeftArcNonExclusiveLocalizedBad gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) u v) :
-- imply
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' u v) ∧ (rlc_dualReflect u ∈ rlc_pathVertices gamma'.1 ∨ (rlc_dualReflect u) 0 = -2 * n ∨ (rlc_dualReflect u) 0 = 2 * n ∨ (rlc_dualReflect u) 1 = -n ∨ (rlc_dualReflect u) 1 = n)) ∨ ∃ p q : Site 2, sharedPrimalEdge u v = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullPhysicalLiftVertexCut A ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' p := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_leftNonExclusiveLocalizedBad_atCut gamma gamma' A hAright hAleft hbad

/--
[rlc_twoChannelFullPhysical_sourceSpliceProvenance_atCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceSpliceProvenance_atCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {ur vr ul vl : Site 2}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A), phb_doubleDualShift a = v) :
-- imply
  ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullPhysicalLiftVertexCut A, phb_doubleDualShift a = v := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceSpliceProvenance_atCut gamma gamma' A hAright hAleft T hTprov

/--
[rlc_twoChannelFullPhysical_axisSourceContact_atCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_axisSourceContact_atCut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {vr vl : Site 2}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (haxis : ∃ v ∈ T.support, v 0 = -1 ∧ (v = vr ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A), a 0 = 0 ∧ phb_doubleDualShift a = v)) :
-- imply
  ∃ v ∈ T.support, v 0 = -1 ∧ (v = vr ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullPhysicalLiftVertexCut A, a 0 = 0 ∧ phb_doubleDualShift a = v) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_axisSourceContact_atCut gamma gamma' A hAright hAleft T haxis

/--
[rlc_twoChannelFullPhysical_wallTerminalProductClassification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallTerminalProductClassification_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hclassR : RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr)
  (hclassL : RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl) :
-- imply
  RlcTwoChannelFullPhysicalWallTerminalProductClassification gamma gamma' omega (vr := vr) (vl := vl) qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallTerminalProductClassification hfaith qr ql hxPath hyPath hclassR hclassL

/--
[rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative_of_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative_of_product_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hproduct : RlcTwoChannelFullPhysicalWallTerminalProductClassification gamma gamma' omega (vr := vr) (vl := vl) qr ql) :
-- imply
  RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative gamma gamma' omega (vr := vr) (vl := vl) qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative_of_product hproduct

/--
[rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hclassR : RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr)
  (hclassL : RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl)
  (hcases : RlcTwoChannelFullPhysicalTetheredWallTerminalFamilyAlternative gamma gamma' omega qr ql) :
-- imply
  RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative gamma gamma' omega (vr := vr) (vl := vl) qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_localizedWallTerminalFamilyAlternative hclassR hclassL hcases

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallTerminalFamilyCases_withDirections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallTerminalFamilyCases_withDirections_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x) (W : (hypercubicLattice 2).Walk ur ul) (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr) (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl), rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr) ∧ (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl) ∧ s(ur, vr) ≠ s(ul, vl) ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ur vr ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ul vl ∧ RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr ∧ RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl ∧ (∀ v ∈ W.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧ RlcTwoChannelFullPhysicalTetheredWallTerminalFamilyAlternative gamma gamma' omega qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallTerminalFamilyCases_withDirections hfaith hxPath hyPath hbad

/--
[rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallTerminalFamilyCases_atMaxCandidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallTerminalFamilyCases_atMaxCandidate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y u : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {hx : x ∈ c.support}
  {hy : y ∈ c.support}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hzMax : ∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hrightPrefix : RlcBookRightPrefixRankAt gamma right)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hbad : RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  ∃ (ur vr ul vl : Site 2) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x) (W : (hypercubicLattice 2).Walk ur ul) (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr) (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl), rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr) ∧ (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl) ∧ s(ur, vr) ≠ s(ul, vl) ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ur vr ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ul vl ∧ RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr ∧ RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl ∧ (∀ v ∈ W.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧ RlcTwoChannelFullPhysicalTetheredWallTerminalFamilyAlternative gamma gamma' omega qr ql ∧ RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative gamma gamma' omega (vr := vr) (vl := vl) qr ql ∧ (RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql → rlc_dualReflect y = rlc_flipX z ∧ RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket gamma gamma' (z := z) (x := x) (y := y) flipLeft ∧ RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateOrderCases gamma gamma' (z := z) (x := x) (y := y) flipLeft ∧ RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceSegmentCases gamma gamma' (z := z) (x := x) (y := y) flipLeft) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGood_tetheredWallTerminalFamilyCases_atMaxCandidate hfaith right flipLeft hzCandidate hzMax hxPath hyPath hxOrder hyOrder hrightPrefix hflipLeftRank hbad

/--
[rlc_twoChannelFullPhysical_twoArcNoGoodFirstBad_of_classified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoArcNoGoodFirstBad_of_classified_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hclassified : RlcTwoChannelFullPhysicalTwoArcClassifiedFirstBadAt gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoArcNoGoodFirstBad_of_classified hno hnoGood c hx hy hxPath hyPath hclassified

/--
[rlc_twoChannelFullPhysical_firstIntersection_twoArcClassified_of_noGood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_firstIntersection_twoArcClassified_of_noGood_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  ∃ (z x y u : Site 2) (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support), c.IsCycle ∧ z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support ∧ rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧ RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧ (∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z) ∧ RlcBookRightIntersectionRankRealizedAt gamma right ∧ RlcBookRightIntersectionRankMinimalAt gamma gamma' right ∧ RlcTwoChannelFullPhysicalTwoArcClassifiedFirstBadAt gamma gamma' omega c hx hy ∧ ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧ ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_firstIntersection_twoArcClassified_of_noGood gamma gamma' hfaith omega hno hnoGood

/--
[rlc_twoChannelFullPhysical_firstIntersection_twoArcNoGood_of_noGood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_firstIntersection_twoArcNoGood_of_noGood_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  ∃ (z x y u : Site 2) (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support), c.IsCycle ∧ z ∈ rlc_pathVertices gamma.1 ∧ rlc_flipX z ∈ rlc_pathVertices gamma'.1 ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support ∧ rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧ RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧ (∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z) ∧ RlcBookRightIntersectionRankRealizedAt gamma right ∧ RlcBookRightIntersectionRankMinimalAt gamma gamma' right ∧ RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy ∧ ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧ ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_firstIntersection_twoArcNoGood_of_noGood gamma gamma' hfaith omega hno hnoGood

/--
[rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstruction_of_noGood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstruction_of_noGood_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt gamma gamma' omega z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstruction_of_noGood gamma gamma' hfaith omega hno hnoGood z hzCandidate

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_fixed_or_laterCandidateObstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_fixed_or_laterCandidateObstruction_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur ul : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
  (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hxz : rlc_dualReflect x = z) :
-- imply
  rlc_dualReflect y = rlc_flipX z ∨ ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧ rlc_bookOrderedCandidateReverseRank gamma q < rlc_bookOrderedCandidateReverseRank gamma z ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt gamma gamma' omega q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_fixed_or_laterCandidateObstruction hfaith hno hnoGood right flipLeft hzRight hzLeft hyPath hyOrder hflipLeftRank hrank hmin qr ql hrow hxz

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowTwo_fixed_or_lowerRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowTwo_fixed_or_lowerRank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {z x y ur ul : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
  (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hxz : rlc_dualReflect x = z) :
-- imply
  rlc_dualReflect y = rlc_flipX z ∨ ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧ rlc_bookOrderedCandidateReverseRank gamma q < rlc_bookOrderedCandidateReverseRank gamma z ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowTwo_fixed_or_lowerRank hfaith A B hAright hAleft hBright hBleft hnoPair right flipLeft hzRight hzLeft hyPath hyOrder hflipLeftRank hrank hmin qr ql hrow hxz

/--
[rlc_twoChannelFullPhysical_noPair_exactRows_fixedRowTwo_or_lowerRank](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_exactRows_fixedRowTwo_or_lowerRank_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {z x y ur ul : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
  (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
  (hrows : RlcTwoChannelFullPhysicalExactOrderedWallTerminalRows gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) flipLeft qr ql) :
-- imply
  RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql ∨ (RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql ∧ rlc_dualReflect x = z ∧ rlc_dualReflect y = rlc_flipX z) ∨ (∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧ rlc_bookOrderedCandidateReverseRank gamma q < rlc_bookOrderedCandidateReverseRank gamma z ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) q) ∨ RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql ∨ RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_exactRows_fixedRowTwo_or_lowerRank hfaith A B hAright hAleft hBright hBleft hnoPair right flipLeft hzRight hzLeft hyPath hyOrder hflipLeftRank hrank hmin qr ql hrows

/--
[rlc_twoChannelFullPhysical_noPair_exactRows_lowerRank_of_rowEliminators](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_exactRows_lowerRank_of_rowEliminators_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {z x y ur ul : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hrank : RlcBookRightIntersectionRankRealizedAt gamma right)
  (hmin : RlcBookRightIntersectionRankMinimalAt gamma gamma' right)
  (hrowOne : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql → rlc_dualReflect x = z → rlc_dualReflect y = (gamma'.1.2.1 : Site 2) → (let W := (rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom; W.support.idxOf (rlc_dualReflect ur) < W.support.idxOf (rlc_dualReflect ul)) → False)
  (hrowTwo : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql → rlc_dualReflect x = z → rlc_dualReflect y = rlc_flipX z → False)
  (hrowThree : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowThree gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql → rlc_dualReflect x = (gamma.1.1 : Site 2) → rlc_dualReflect y = (gamma'.1.2.1 : Site 2) → (∃ (hzR : rlc_flipX z ∈ (((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).support) (hzL : z ∈ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support), rlc_dualReflect ur ∈ ((((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse).dropUntil (rlc_flipX z) hzR).support ∧ rlc_dualReflect ul ∈ (((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).dropUntil z hzL).support) → False)
  (hrowFour : ∀ r : Site 2, RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowFour gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql → rlc_dualReflect x = (gamma.1.1 : Site 2) → r ∈ rlc_pathVertices gamma.1 → rlc_dualReflect y = rlc_flipX r → r ∈ flipLeft.support → (let W := ((rlc_ambientCrossingWalk gamma.1).map rlc_flipXLatticeHom).reverse; W.support.idxOf (rlc_dualReflect ul) < W.support.idxOf (rlc_dualReflect ur)) → False)
  (hrows : RlcTwoChannelFullPhysicalExactOrderedWallTerminalRows gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) flipLeft qr ql) :
-- imply
  ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧ rlc_bookOrderedCandidateReverseRank gamma q < rlc_bookOrderedCandidateReverseRank gamma z ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_exactRows_lowerRank_of_rowEliminators hfaith A B hAright hAleft hBright hBleft hnoPair right flipLeft hzRight hzLeft hyPath hyOrder hflipLeftRank hrank hmin qr ql hrowOne hrowTwo hrowThree hrowFour hrows

/--
[rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstructionOnCycle_of_noGood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstructionOnCycle_of_noGood_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {z : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hcycle : c.IsCycle)
  (haSupport : a ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (haCycle : a ∈ c.support)
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle gamma gamma' omega c z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_orderedCandidateNoGoodObstructionOnCycle_of_noGood gamma gamma' hfaith omega hno hnoGood c hcycle haSupport haCycle z hzCandidate

/--
[rlc_twoChannelFullPhysical_exists_globalOrderedCandidateNoGoodObstructionCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_exists_globalOrderedCandidateNoGoodObstructionCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u), c.IsCycle ∧ rlc_twoChannelFullFilledReachSet gamma gamma' omega = jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧ ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle gamma gamma' omega c z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_exists_globalOrderedCandidateNoGoodObstructionCycle gamma gamma' hfaith omega hno hnoGood

/--
[rlc_twoChannelFullPhysical_staticCutFailure_globalOrderedObstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_staticCutFailure_globalOrderedObstruction_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hfailure : ¬∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable x y) :
-- imply
  let omega := rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A ∃ (u : Site 2) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u), c.IsCycle ∧ rlc_twoChannelFullFilledReachSet gamma gamma' omega = jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧ rlc_twoChannelFullReachSet gamma gamma' omega ⊆ rlc_twoChannelFullPhysicalLiftVertexCut A ∧ ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle gamma gamma' omega c z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_staticCutFailure_globalOrderedObstruction gamma gamma' hfaith A hAright hAleft hfailure

/--
[rlc_twoChannelFullPhysical_fixedExtremalContactsOnCycle_of_failure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_fixedExtremalContactsOnCycle_of_failure_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hcycle : c.IsCycle)
  (haSupport : a ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (haCycle : a ∈ c.support) :
-- imply
  ∃ x y : Site 2, x ∈ c.support ∧ y ∈ c.support ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', ∃ (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)), rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support ∧ rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧ RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧ RlcBookRightIntersectionRankRealizedAt gamma right ∧ RlcBookRightPrefixRankAt gamma right := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_fixedExtremalContactsOnCycle_of_failure gamma gamma' hfaith omega hno c hcycle haSupport haCycle

/--
[rlc_twoChannelFullPhysical_fixedContactNoGoodObstructionOnCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_fixedContactNoGoodObstructionOnCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hcycle : c.IsCycle)
  (haSupport : a ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (haCycle : a ∈ c.support) :
-- imply
  ∃ (x y : Site 2) (hx : x ∈ c.support) (hy : y ∈ c.support), rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy ∧ ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧ ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) ∧ ∀ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', ∃ (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)), rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support ∧ rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧ RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧ RlcBookRightIntersectionRankRealizedAt gamma right ∧ RlcBookRightPrefixRankAt gamma right := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_fixedContactNoGoodObstructionOnCycle gamma gamma' hfaith omega hno hnoGood c hcycle haSupport haCycle

/--
[rlc_twoChannelFullPhysical_staticCutFailure_extremalObstructionsOnCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_staticCutFailure_extremalObstructionsOnCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hfailure : ¬∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable x y) :
-- imply
  let omega := rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A ∃ (u : Site 2) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u) (zMin zMax : Site 2), c.IsCycle ∧ rlc_twoChannelFullFilledReachSet gamma gamma' omega = jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧ rlc_twoChannelFullReachSet gamma gamma' omega ⊆ rlc_twoChannelFullPhysicalLiftVertexCut A ∧ zMin ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧ zMax ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧ (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf zMin ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf q) ∧ (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf zMax) ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle gamma gamma' omega c zMin ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle gamma gamma' omega c zMax := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_staticCutFailure_extremalObstructionsOnCycle gamma gamma' hfaith A hAright hAleft hfailure

/--
[rlc_twoChannelFullPhysical_extremalOrderedCandidateNoGoodObstructionsOnCycle_of_noGood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_extremalOrderedCandidateNoGoodObstructionsOnCycle_of_noGood_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  ∃ (u : Site 2) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u) (zMin zMax : Site 2), c.IsCycle ∧ rlc_twoChannelFullFilledReachSet gamma gamma' omega = jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∧ zMin ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧ zMax ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧ (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf zMin ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf q) ∧ (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf zMax) ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle gamma gamma' omega c zMin ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle gamma gamma' omega c zMax := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_extremalOrderedCandidateNoGoodObstructionsOnCycle_of_noGood gamma gamma' hfaith omega hno hnoGood

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition_reselect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition_reselect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hbracket : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  (rlc_dualReflect x = z ∧ rlc_dualReflect y = rlc_flipX z) ∨ (∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q < (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt gamma gamma' omega q) ∨ ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt gamma gamma' omega q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition_reselect gamma gamma' hfaith omega hno hnoGood hzCandidate hyPath hflipLeftRank hbracket

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition_reselectOnCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition_reselectOnCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hcycle : c.IsCycle)
  (haSupport : a ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support)
  (haCycle : a ∈ c.support)
  (hzCandidate : z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma')
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hflipLeftRank : RlcBookReflectedLeftSuffixRankAt gamma' flipLeft)
  (hbracket : RlcTwoChannelFullPhysicalWallFamilyRowTwoCandidateBracket gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  (rlc_dualReflect x = z ∧ rlc_dualReflect y = rlc_flipX z) ∨ (∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q < (rlc_ambientCrossingWalk gamma.1).support.idxOf z ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle gamma gamma' omega c q) ∨ ∃ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z < (rlc_ambientCrossingWalk gamma.1).support.idxOf q ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionOnCycle gamma gamma' omega c q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_candidateTransition_reselectOnCycle gamma gamma' hfaith omega hno hnoGood c hcycle haSupport haCycle hzCandidate hyPath hflipLeftRank hbracket

/--
[rlc_twoChannelFullPhysical_extremalOrderedCandidateNoGoodObstructions_of_noGood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_extremalOrderedCandidateNoGoodObstructions_of_noGood_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  ∃ zMin zMax : Site 2, zMin ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧ zMax ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧ (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf zMin ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf q) ∧ (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf zMax) ∧ (rlc_ambientCrossingWalk gamma.1).support.idxOf zMin ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf zMax ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt gamma gamma' omega zMin ∧ RlcTwoChannelFullPhysicalOrderedCandidateNoGoodObstructionAt gamma gamma' omega zMax := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_extremalOrderedCandidateNoGoodObstructions_of_noGood gamma gamma' hfaith omega hno hnoGood

/--
[rlc_finiteBidirectionalStrictRankTransition_twoCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_finiteBidirectionalStrictRankTransition_twoCycle_eq :
-- imply
  ∃ (states : Finset Nat) (next : Nat → Nat), RlcFiniteBidirectionalStrictRankTransition states id next ∧ 0 ∈ states ∧ next 0 ≠ 0 ∧ next (next 0) = 0 := by
-- proof
  apply StatMech.Universality.rlc_finiteBidirectionalStrictRankTransition_twoCycle

/--
[rlc_twoChannelFullPhysical_maxOrderedIntersection_twoArcNoGood_of_noGood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_maxOrderedIntersection_twoArcNoGood_of_noGood_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  ∃ (z x y u : Site 2) (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support), c.IsCycle ∧ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧ (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf q ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf z) ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support ∧ rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧ RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧ RlcBookRightIntersectionRankRealizedAt gamma right ∧ RlcBookRightPrefixRankAt gamma right ∧ RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy ∧ ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧ ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_maxOrderedIntersection_twoArcNoGood_of_noGood gamma gamma' hfaith omega hno hnoGood

/--
[rlc_twoChannelFullPhysical_minOrderedIntersection_twoArcNoGood_of_noGood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_minOrderedIntersection_twoArcNoGood_of_noGood_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  ∃ (z x y u : Site 2) (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z) (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)) (c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u) (hx : x ∈ c.support) (hy : y ∈ c.support), c.IsCycle ∧ z ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma' ∧ (∀ q ∈ rlc_bookOrderedIntersectionCandidateSet gamma gamma', (rlc_ambientCrossingWalk gamma.1).support.idxOf z ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf q) ∧ rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧ rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support ∧ rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support ∧ RlcBookReflectedLeftSuffixRankAt gamma' flipLeft ∧ RlcBookRightIntersectionRankRealizedAt gamma right ∧ RlcBookRightPrefixRankAt gamma right ∧ RlcTwoChannelFullPhysicalTwoArcNoGoodFirstBadAt gamma gamma' omega c hx hy ∧ ((x 0 = -1 ∧ x 1 < -1) ∨ x 0 < -1) ∧ ((y 0 = -1 ∧ 0 ≤ y 1) ∨ 0 ≤ y 0) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_minOrderedIntersection_twoArcNoGood_of_noGood gamma gamma' hfaith omega hno hnoGood

/--
[rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hside : RlcTwoChannelFullPhysicalContourArcSide gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalFilledBoundarySegment gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcSide c hx hy hxPath hyPath hside

/--
[rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contactCycleCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contactCycleCertificate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hcertificate : RlcTwoChannelFullPhysicalContactCycleCertificate gamma gamma' omega) :
-- imply
  RlcTwoChannelFullPhysicalFilledBoundarySegment gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contactCycleCertificate hcertificate

/--
[rlc_twoChannelFullPhysicalGoodComponentContacts_of_contactCycleCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalGoodComponentContacts_of_contactCycleCertificate_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hcertificate : RlcTwoChannelFullPhysicalContactCycleCertificate gamma gamma' omega) :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalGoodComponentContacts_of_contactCycleCertificate hcertificate

/--
[rlc_twoChannelFullPhysicalContactCycleCertificate_of_goodComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalContactCycleCertificate_of_goodComponent_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hcomponent : RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  RlcTwoChannelFullPhysicalContactCycleCertificate gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalContactCycleCertificate_of_goodComponent hfaith hcomponent

/--
[rlc_twoChannelFullPhysicalContactCycleCertificate_iff_goodComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalContactCycleCertificate_iff_goodComponent_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalContactCycleCertificate gamma gamma' omega ↔ RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalContactCycleCertificate_iff_goodComponent hfaith omega

/--
[rlc_twoChannelFullPhysicalContactCycleSelection_iff_goodComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalContactCycleSelection_iff_goodComponents_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalContactCycleSelection gamma gamma' hfaith ↔ ∀ omega : RlcTwoChannelEdgeConfig gamma gamma', rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' → RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalContactCycleSelection_iff_goodComponents hfaith

/--
[rlc_twoChannelFullPhysicalFilledBoundarySegment_of_goodComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalFilledBoundarySegment_of_goodComponent_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hcomponent : RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  RlcTwoChannelFullPhysicalFilledBoundarySegment gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalFilledBoundarySegment_of_goodComponent hcomponent

/--
[rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcRepairSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcRepairSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSide gamma gamma' omega c hx hy) :
-- imply
  RlcTwoChannelFullPhysicalFilledBoundarySegment gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalFilledBoundarySegment_of_contourArcRepairSide c hx hy hxPath hyPath hrepair

/--
[rlc_twoChannelFullPhysicalPermConfig_success_of_filledBoundarySegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_success_of_filledBoundarySegment_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hsegment : RlcTwoChannelFullPhysicalFilledBoundarySegment gamma gamma' omega) :
-- imply
  rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_success_of_filledBoundarySegment omega hsegment

/--
[rlc_twoChannelFullPhysicalPermConfig_success_of_contourArcRepairSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermConfig_success_of_contourArcRepairSide_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSide gamma gamma' omega c hx hy) :
-- imply
  rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalPermConfig gamma gamma' omega) ∈ rlc_finiteTwoChannelConnectorEvent gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermConfig_success_of_contourArcRepairSide omega c hx hy hxPath hyPath hrepair

/--
[rlc_twoChannelFullPhysicalRetainedSideSelection_of_contourArcRepairSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalRetainedSideSelection_of_contourArcRepairSelection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSelection gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalRetainedSideSelection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalRetainedSideSelection_of_contourArcRepairSelection hfaith hrepair

/--
[rlc_twoChannelFullPhysicalStaticCutIntersection_of_retainedSideSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutIntersection_of_retainedSideSelection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hselection : RlcTwoChannelFullPhysicalRetainedSideSelection gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutIntersection_of_retainedSideSelection hfaith hselection

/--
[rlc_twoChannelFullPhysicalRetainedSideSelection_of_goodComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalRetainedSideSelection_of_goodComponents_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hcomponents : ∀ omega : RlcTwoChannelEdgeConfig gamma gamma', rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma' → RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega) :
-- imply
  RlcTwoChannelFullPhysicalRetainedSideSelection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalRetainedSideSelection_of_goodComponents hfaith hcomponents

/--
[rlc_twoChannelFullPhysicalPermutationSuccess_of_retainedSideSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermutationSuccess_of_retainedSideSelection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hselection : RlcTwoChannelFullPhysicalRetainedSideSelection gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermutationSuccess_of_retainedSideSelection hfaith hselection

/--
[rlc_twoChannelFullPhysicalPermutationSuccess_of_contourArcRepairSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermutationSuccess_of_contourArcRepairSelection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hrepair : RlcTwoChannelFullPhysicalContourArcRepairSelection gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermutationSuccess_of_contourArcRepairSelection hfaith hrepair

/--
[rlc_twoChannelFullPhysicalRetainedSideSelection_of_contactCycleSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalRetainedSideSelection_of_contactCycleSelection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hselection : RlcTwoChannelFullPhysicalContactCycleSelection gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalRetainedSideSelection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalRetainedSideSelection_of_contactCycleSelection hfaith hselection

/--
[rlc_twoChannelFullPhysicalStaticCutIntersection_of_contactCycleSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutIntersection_of_contactCycleSelection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hselection : RlcTwoChannelFullPhysicalContactCycleSelection gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalStaticCutIntersection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutIntersection_of_contactCycleSelection hfaith hselection

/--
[rlc_twoChannelFullPhysicalGoodComponentContacts_of_staticCutConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalGoodComponentContacts_of_staticCutConnectivity_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith)
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalGoodComponentContacts_of_staticCutConnectivity hfaith hstatic omega hno

/--
[rlc_twoChannelFullPhysicalContactCycleSelection_of_staticCutConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalContactCycleSelection_of_staticCutConnectivity_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hstatic : RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalContactCycleSelection gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalContactCycleSelection_of_staticCutConnectivity hfaith hstatic

/--
[rlc_twoChannelFullPhysicalContactCycleSelection_iff_staticCutConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalContactCycleSelection_iff_staticCutConnectivity_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalContactCycleSelection gamma gamma' hfaith ↔ RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalContactCycleSelection_iff_staticCutConnectivity hfaith

/--
[rlc_twoChannelFullPhysicalStaticCutConnectivity_iff_cutInteriorGoodComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalStaticCutConnectivity_iff_cutInteriorGoodComponents_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma') :
-- imply
  RlcTwoChannelFullPhysicalStaticCutConnectivity gamma gamma' hfaith ↔ ∀ (A : Set (RlcConnectorVertex n)), (∀ x, rlc_connectorOnRight gamma x → x ∈ A) → (∀ y, rlc_connectorOnLeft gamma' y → y ∉ A) → RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalStaticCutConnectivity_iff_cutInteriorGoodComponents hfaith

/--
[rlc_twoChannelFullPhysicalPermutationSuccess_of_contactCycleSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysicalPermutationSuccess_of_contactCycleSelection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hselection : RlcTwoChannelFullPhysicalContactCycleSelection gamma gamma' hfaith) :
-- imply
  RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysicalPermutationSuccess_of_contactCycleSelection hfaith hselection

/--
[rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPhysicalSuccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPhysicalSuccess_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith) :
-- imply
  RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPhysicalSuccess hclosure hfaith hphysical

/--
[rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_fullPhysicalSuccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_fullPhysicalSuccess_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {N : Nat}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith)
  (hq : 1 <= q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  rlc_twoChannelForcedDualEventMass gamma gamma' (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma')ᶜ <= (Real.sqrt q) ^ N * FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorMergedWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualEventMass_compl_le_sqrt_pow_merged_of_fullPhysicalSuccess hclosure hfaith hphysical hq N hscore

/--
[rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_fullPhysicalSuccess_scoreDefect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_fullPhysicalSuccess_scoreDefect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {q : Real}
  {N : Nat}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith)
  (hq : 1 <= q)
  (hscore : RlcTwoChannelFullPhysicalPermutationScoreDefect gamma gamma' N) :
-- imply
  1 / (1 + (Real.sqrt q) ^ N * q) <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint q) q (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_selfDual_ge_of_fullPhysicalSuccess_scoreDefect hclosure hfaith hphysical hq N hscore

/--
[rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_fullPhysicalSuccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_fullPhysicalSuccess_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith) :
-- imply
  RlcTwoChannelForcedDualFailurePushforwardComparison gamma gamma' 1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelForcedDualFailurePushforwardComparison_q_one_of_fullPhysicalSuccess hclosure hfaith hphysical

/--
[rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_fullPhysicalSuccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_fullPhysicalSuccess_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hphysical : RlcTwoChannelFullPhysicalPermutationSuccess gamma gamma' hfaith) :
-- imply
  (1 / 2 : Real) <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint 1) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_fullPhysicalSuccess hclosure hfaith hphysical

/--
[rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_contactCycleSelection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_contactCycleSelection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hselection : RlcTwoChannelFullPhysicalContactCycleSelection gamma gamma' hfaith) :
-- imply
  (1 / 2 : Real) <= FK.bcEventMass (rlc_connectorTwoChannelGraph gamma gamma') (rlc_connectorSeparateWiring gamma gamma') (BeffaraDC.selfDualPoint 1) 1 (rlc_finiteTwoChannelConnectorEvent gamma gamma') := by
-- proof
  apply StatMech.Universality.rlc_finiteTwoChannelConnectorMass_selfDual_ge_half_of_contactCycleSelection hclosure hfaith hselection

/--
[rlc_walk_idxOf_le_of_getVert_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_idxOf_le_of_getVert_eq_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b z : V}
  {W : G.Walk a b}
  {k : Nat}
-- given
  (hk : k ≤ W.length)
  (hget : W.getVert k = z) :
-- imply
  W.support.idxOf z ≤ k := by
-- proof
  apply StatMech.Universality.rlc_walk_idxOf_le_of_getVert_eq W hk hget

/--
[rlc_walk_exists_contact_extrema_around_offSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_exists_contact_extrema_around_offSupport_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b u : V}
  {W : G.Walk a b}
  {C : G.Walk u u}
  {k : Nat}
-- given
  (hkLength : k ≤ W.length)
  (ha : a ∈ C.support)
  (hb : b ∈ C.support)
  (hkOff : W.getVert k ∉ C.support) :
-- imply
  ∃ i j : Nat, i < k ∧ k < j ∧ j ≤ W.length ∧ W.getVert i ∈ C.support ∧ W.getVert j ∈ C.support ∧ ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
-- proof
  apply StatMech.Universality.rlc_walk_exists_contact_extrema_around_offSupport W C hkLength ha hb hkOff

/--
[rlc_walk_exists_contact_extrema_around_offSupport_of_contacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_exists_contact_extrema_around_offSupport_of_contacts_eq
  [DecidableEq V]
  {G K : SimpleGraph V}
  {a b u : V}
  {W : G.Walk a b}
  {C : K.Walk u u}
  {k : Nat}
-- given
  (hkOff : W.getVert k ∉ C.support)
  (hbefore : ∃ i : Nat, i < k ∧ W.getVert i ∈ C.support)
  (hafter : ∃ j : Nat, k < j ∧ j ≤ W.length ∧ W.getVert j ∈ C.support) :
-- imply
  ∃ i j : Nat, i < k ∧ k < j ∧ j ≤ W.length ∧ W.getVert i ∈ C.support ∧ W.getVert j ∈ C.support ∧ ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
-- proof
  apply StatMech.Universality.rlc_walk_exists_contact_extrema_around_offSupport_of_contacts W C hkOff hbefore hafter

/--
[rlc_walk_prefix_reversePrefix_contact_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_prefix_reversePrefix_contact_interval_eq
  [DecidableEq V]
  {G K : SimpleGraph V}
  {a b u z : V}
  {W : G.Walk a b}
  {C : K.Walk u u}
-- given
  (hzW : z ∈ W.support)
  (hzC : z ∉ C.support)
  (hprefix : ∃ v ∈ (W.takeUntil z hzW).support, v ∈ C.support)
  (hsuffix : ∃ v ∈ (W.reverse.takeUntil z (by simpa [SimpleGraph.Walk.support_reverse] using hzW)).support, v ∈ C.support) :
-- imply
  ∃ i j : Nat, i < W.support.idxOf z ∧ W.support.idxOf z < j ∧ j ≤ W.length ∧ W.getVert i ∈ C.support ∧ W.getVert j ∈ C.support ∧ ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
-- proof
  apply StatMech.Universality.rlc_walk_prefix_reversePrefix_contact_interval W C hzW hzC hprefix hsuffix

/--
[rlc_walk_exists_edge_index](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_exists_edge_index_eq
  {G : SimpleGraph V}
  {a b x y : V}
  {W : G.Walk a b}
-- given
  (hxy : s(x, y) ∈ W.edges) :
-- imply
  ∃ k : Nat, k < W.length ∧ ((W.getVert k = x ∧ W.getVert (k + 1) = y) ∨ (W.getVert k = y ∧ W.getVert (k + 1) = x)) := by
-- proof
  apply StatMech.Universality.rlc_walk_exists_edge_index W hxy

/--
[rlc_walk_edge_prefix_reversePrefix_contact_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_edge_prefix_reversePrefix_contact_interval_eq
  [DecidableEq V]
  {G K : SimpleGraph V}
  {a b u x y zR zL : V}
  {W : G.Walk a b}
  {C : K.Walk u u}
-- given
  (hxy : s(x, y) ∈ W.edges)
  (hzR : zR ∈ s(x, y))
  (hzL : zL ∈ s(x, y))
  (hedgeOff : ∀ z ∈ s(x, y), z ∉ C.support)
  (hzRW : zR ∈ W.support)
  (hzLWRev : zL ∈ W.reverse.support)
  (hprefix : ∃ v ∈ (W.takeUntil zR hzRW).support, v ∈ C.support)
  (hsuffix : ∃ v ∈ (W.reverse.takeUntil zL hzLWRev).support, v ∈ C.support) :
-- imply
  ∃ k i j : Nat, k < W.length ∧ s(W.getVert k, W.getVert (k + 1)) = s(x, y) ∧ i < k ∧ k + 1 < j ∧ j ≤ W.length ∧ W.getVert i ∈ C.support ∧ W.getVert j ∈ C.support ∧ ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
-- proof
  apply StatMech.Universality.rlc_walk_edge_prefix_reversePrefix_contact_interval W C hxy hzR hzL hedgeOff hzRW hzLWRev hprefix hsuffix

/--
[rlc_walk_support_subset_loop_or_contact_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_support_subset_loop_or_contact_interval_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b u : V}
  {W : G.Walk a b}
  {C : G.Walk u u}
-- given
  (ha : a ∈ C.support)
  (hb : b ∈ C.support) :
-- imply
  (∀ z ∈ W.support, z ∈ C.support) ∨ ∃ k i j : Nat, i < k ∧ k < j ∧ j ≤ W.length ∧ W.getVert k ∉ C.support ∧ W.getVert i ∈ C.support ∧ W.getVert j ∈ C.support ∧ ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support := by
-- proof
  apply StatMech.Universality.rlc_walk_support_subset_loop_or_contact_interval W C ha hb

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisContactInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisContactInterval_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {T : (hypercubicLattice 2).Walk vr vl}
-- given
  (hvrC : vr ∈ c.support)
  (hvlC : vl ∈ c.support)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) :
-- imply
  ∃ (v : Site 2) (k : Nat), k ≤ T.length ∧ T.getVert k = v ∧ v 0 = -1 ∧ (v ∈ c.support ∨ ∃ i j : Nat, i < k ∧ k < j ∧ j ≤ T.length ∧ T.getVert i ∈ c.support ∧ T.getVert j ∈ c.support ∧ ∀ l : Nat, i < l → l < j → T.getVert l ∉ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_axisContactInterval c hvrC hvlC hrow hurv hulv T hTprov

/--
[rlc_walk_ordered_to_complementary_contact_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_ordered_to_complementary_contact_interval_eq
  {G K : SimpleGraph (Site 2)}
  {u x y a b : Site 2}
  {c : G.Walk u u}
  {W : K.Walk a b}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (ha : a ∈ (rlc_orderedContourArc c hx hy).support)
  (hb : b ∈ (rlc_complementaryContourArc c hx hy).support) :
-- imply
  (∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c hx hy).support ∧ z ∈ (rlc_complementaryContourArc c hx hy).support) ∨ ∃ i j : Nat, i < j ∧ j ≤ W.length ∧ W.getVert i ∈ (rlc_orderedContourArc c hx hy).support ∧ W.getVert j ∈ (rlc_complementaryContourArc c hx hy).support ∧ ∀ l : Nat, i < l → l < j → W.getVert l ∉ c.support := by
-- proof
  apply StatMech.Universality.rlc_walk_ordered_to_complementary_contact_interval c hx hy W ha hb

/--
[rlc_twoChannelFullPhysical_twoFirstBad_cycleSupport_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoFirstBad_cycleSupport_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y ur vr ul vl k : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr))
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl))
  (hk : k ∈ c.support) :
-- imply
  k ∈ qr.support ∨ k = ur ∨ k = vr ∨ k ∈ rr.support ∨ k ∈ ql.support ∨ k = ul ∨ k = vl ∨ k ∈ rl.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoFirstBad_cycleSupport_cases c hx hy qr rr ql rl hurv hulv hdecR hdecL hk

/--
[rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y ur vr ul vl f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr))
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl))
  (hfgCycle : s(f, g) ∈ c.edges)
  (hfgBad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
-- imply
  s(f, g) = s(ur, vr) ∨ s(f, g) ∈ rr.edges ∨ s(f, g) = s(ul, vl) ∨ s(f, g) ∈ rl.edges := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_cases c hx hy qr rr ql rl hurv hulv hdecR hdecL hfgCycle hfgBad

/--
[rlc_twoChannelFullPhysical_noncarrierEdge_eq_firstExit_or_mem_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noncarrierEdge_eq_firstExit_or_mem_remainder_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y u v f g : Site 2}
  {w : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
  {r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v y}
-- given
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hdecomp : w = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons huv r))
  (hfg : s(f, g) ∈ w.edges)
  (hfgBad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
-- imply
  s(f, g) = s(u, v) ∨ s(f, g) ∈ r.edges := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noncarrierEdge_eq_firstExit_or_mem_remainder w q r huv hdecomp hfg hfgBad

/--
[rlc_twoChannelFullPhysical_firstExit_of_noncarrierEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_firstExit_of_noncarrierEdge_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y f g : Site 2}
  {w : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y}
-- given
  (hfg : s(f, g) ∈ w.edges)
  (hfgBad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
-- imply
  ∃ (u v : Site 2) (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u) (r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v y) (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v), ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u v ∧ w = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons huv r) ∧ (s(f, g) = s(u, v) ∨ s(f, g) ∈ r.edges) ∧ r.length < w.length := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_firstExit_of_noncarrierEdge_mem w hfg hfgBad

/--
[rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_exact_or_reverseFirstExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_exact_or_reverseFirstExit_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y ur vr ul vl f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr))
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl))
  (hfgCycle : s(f, g) ∈ c.edges)
  (hfgBad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
-- imply
  s(f, g) = s(ur, vr) ∨ (∃ (u' v' : Site 2) (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y u') (r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v' vr) (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u' v'), ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u' v' ∧ rr.reverse = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons huv r) ∧ (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧ r.length < rr.length) ∨ s(f, g) = s(ul, vl) ∨ ∃ (u' v' : Site 2) (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u') (r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v' vl) (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u' v'), ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u' v' ∧ rl.reverse = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons huv r) ∧ (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧ r.length < rl.length := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_exact_or_reverseFirstExit c hx hy qr rr ql rl hurv hulv hdecR hdecL hfgCycle hfgBad

/--
[rlc_twoChannelFullPhysical_rightArcClassifiedBad_of_goodPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rightArcClassifiedBad_of_goodPrefix_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x u v : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u v) :
-- imply
  RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega u v := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rightArcClassifiedBad_of_goodPrefix hno hnoGood hxPath q huv hbad

/--
[rlc_twoChannelFullPhysical_goodReachable_of_rightClassifiedBadRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodReachable_of_rightClassifiedBadRepairs_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y : Site 2}
  {a : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk x y}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hrepair : ∀ {u v : Site 2}, RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega u v → ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u v → (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable u v) :
-- imply
  (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable x y := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodReachable_of_rightClassifiedBadRepairs hno hnoGood hxPath a hrepair

/--
[rlc_twoChannelFullPhysical_goodComponent_of_rightClassifiedBadRepairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_goodComponent_of_rightClassifiedBadRepairs_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrepair : ∀ {f g : Site 2}, RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega f g → ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g → (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable f g) :
-- imply
  RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_goodComponent_of_rightClassifiedBadRepairs hno hnoGood c hx hy hxPath hyPath hrepair

/--
[rlc_twoChannelFullPhysical_firstUnrepairableRightClassifiedBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_firstUnrepairableRightClassifiedBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ (ur vr : Site 2) (qRepair : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph gamma gamma' omega).Walk x ur) (qGood : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y) (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr), rlc_orderedContourArc c hx hy = (qRepair.mapLe (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr) ∧ rr.length < (rlc_orderedContourArc c hx hy).length ∧ ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable ur vr ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ur vr ∧ RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_firstUnrepairableRightClassifiedBad hno hnoGood c hx hy hxPath hyPath

/--
[rlc_twoChannelFullPhysical_leftArcClassifiedBad_of_goodPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_leftArcClassifiedBad_of_goodPrefix_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {y u v : Site 2}
  {q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y u}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u v)
  (hbad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u v) :
-- imply
  RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega u v := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_leftArcClassifiedBad_of_goodPrefix hno hnoGood hyPath q huv hbad

/--
[rlc_twoChannelFullPhysical_firstUnrepairableLeftClassifiedBad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_firstUnrepairableLeftClassifiedBad_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ (ul vl : Site 2) (qRepair : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph gamma gamma' omega).Walk y ul) (qGood : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x) (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl), (rlc_complementaryContourArc c hx hy).reverse = (qRepair.mapLe (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl) ∧ rl.length < (rlc_complementaryContourArc c hx hy).reverse.length ∧ ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable ul vl ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ul vl ∧ RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_firstUnrepairableLeftClassifiedBad hno hnoGood c hx hy hxPath hyPath

/--
[rlc_twoChannelFullPhysical_unrepairableTerminalProductClassification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_unrepairableTerminalProductClassification_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1) :
-- imply
  ∃ (ur vr ul vl : Site 2) (qRepairR : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph gamma gamma' omega).Walk x ur) (qRepairL : (rlc_twoChannelFullPhysicalRepairableBoundaryGraph gamma gamma' omega).Walk y ul) (qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur) (ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul) (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x) (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr) (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl), rlc_orderedContourArc c hx hy = (qRepairR.mapLe (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr) ∧ (rlc_complementaryContourArc c hx hy).reverse = (qRepairL.mapLe (rlc_twoChannelFullPhysicalRepairableBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl) ∧ rr.length < (rlc_orderedContourArc c hx hy).length ∧ rl.length < (rlc_complementaryContourArc c hx hy).reverse.length ∧ ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable ur vr ∧ ¬(rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Reachable ul vl ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ur vr ∧ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' ul vl ∧ RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr ∧ RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl ∧ RlcTwoChannelFullPhysicalWallTerminalProductClassification gamma gamma' omega (vr := vr) (vl := vl) qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_unrepairableTerminalProductClassification hfaith hno hnoGood c hx hy hxPath hyPath

/--
[rlc_twoChannelFullPhysical_orderedWallAlternative_of_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_orderedWallAlternative_of_product_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur vr ul vl : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hfirst : ∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
  (hproduct : RlcTwoChannelFullPhysicalWallTerminalProductClassification gamma gamma' omega (vr := vr) (vl := vl) qr ql) :
-- imply
  (∃ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∉ rlc_connectorFourTraceEdges gamma gamma') ∨ (∃ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∉ rlc_connectorFourTraceEdges gamma gamma') ∨ RlcTwoChannelFullPhysicalRightArcNonExclusiveLocalizedBad gamma gamma' omega ur vr ∨ RlcTwoChannelFullPhysicalLeftArcNonExclusiveLocalizedBad gamma gamma' omega ul vl ∨ (RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyTable gamma gamma' omega qr ql ∧ RlcTwoChannelFullPhysicalOrderedWallFamilyOutcome gamma gamma' omega flipLeft qr ql) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_orderedWallAlternative_of_product hfaith hnoGood right flipLeft hzRight hzLeft hxPath hyPath hxOrder hyOrder hfirst qr ql hproduct

/--
[rlc_twoChannelFullPhysical_exactOrderedWallAlternative_of_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_exactOrderedWallAlternative_of_product_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z x y ur vr ul vl : Site 2}
  {right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxOrder : rlc_flipX (rlc_dualReflect x) ∈ (right.map rlc_flipXLatticeHom).support)
  (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support)
  (hfirst : ∀ w ∈ right.support, rlc_flipX w ∈ rlc_pathVertices gamma'.1 → w = z)
  (hproduct : RlcTwoChannelFullPhysicalWallTerminalProductClassification gamma gamma' omega (vr := vr) (vl := vl) qr ql) :
-- imply
  (∃ e ∈ qr.edges, Sym2.map rlc_dualReflect e ∉ rlc_connectorFourTraceEdges gamma gamma') ∨ (∃ e ∈ ql.edges, Sym2.map rlc_dualReflect e ∉ rlc_connectorFourTraceEdges gamma gamma') ∨ RlcTwoChannelFullPhysicalRightArcNonExclusiveLocalizedBad gamma gamma' omega ur vr ∨ RlcTwoChannelFullPhysicalLeftArcNonExclusiveLocalizedBad gamma gamma' omega ul vl ∨ RlcTwoChannelFullPhysicalExactOrderedWallTerminalRows gamma gamma' omega flipLeft qr ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_exactOrderedWallAlternative_of_product hfaith hnoGood right flipLeft hzRight hzLeft hxPath hyPath hxOrder hyOrder hfirst qr ql hproduct

/--
[rlc_twoChannelFullPhysical_staticCutFailure_unrepairableTerminalProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_staticCutFailure_unrepairableTerminalProduct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hfailure : ¬∃ x y : RlcConnectorVertex n, rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧ (rlc_twoChannelFullPhysicalCutTargetGraphAt gamma gamma' A).Reachable x y) :
-- imply
  RlcTwoChannelFullPhysicalUnrepairableTerminalProductObstruction gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_staticCutFailure_unrepairableTerminalProduct gamma gamma' hfaith A hAright hAleft hfailure

/--
[rlc_twoChannelFullPhysical_noPair_unrepairableTerminalProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_unrepairableTerminalProduct_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1) :
-- imply
  RlcTwoChannelFullPhysicalUnrepairableTerminalProductObstruction gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_unrepairableTerminalProduct gamma gamma' hfaith A B hAright hAleft hBright hBleft hnoPair

/--
[rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_product_or_shorter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_product_or_shorter_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y ur vr ul vl f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr))
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl))
  (hclassR : RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega ur vr)
  (hclassL : RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega ul vl)
  (hfgCycle : s(f, g) ∈ c.edges)
  (hfgBad : ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) :
-- imply
  s(f, g) = s(ur, vr) ∨ (∃ (u' v' : Site 2) (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y u') (r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v' vr) (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u' v'), ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u' v' ∧ rr.reverse = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons huv r) ∧ (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧ r.length < rr.length ∧ r.length + rl.length < rr.length + rl.length ∧ RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' omega u' v' ∧ RlcTwoChannelFullPhysicalWallTerminalProductClassification gamma gamma' omega (vr := vr) (vl := v') qr q ∧ RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative gamma gamma' omega (vr := vr) (vl := v') qr q) ∨ s(f, g) = s(ul, vl) ∨ ∃ (u' v' : Site 2) (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x u') (r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk v' vl) (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj u' v'), ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u' v' ∧ rl.reverse = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons huv r) ∧ (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧ r.length < rl.length ∧ rr.length + r.length < rr.length + rl.length ∧ RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' omega u' v' ∧ RlcTwoChannelFullPhysicalWallTerminalProductClassification gamma gamma' omega (vr := v') (vl := vl) q ql ∧ RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative gamma gamma' omega (vr := v') (vl := vl) q ql := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_twoFirstBad_noncarrierEdge_product_or_shorter hfaith hno hnoGood c hx hy hxPath hyPath qr rr ql rl hurv hulv hdecR hdecL hclassR hclassL hfgCycle hfgBad

/--
[rlc_twoChannelFullPhysical_noPair_BChanging_terminal_or_strictSuffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_BChanging_terminal_or_strictSuffix_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u x y ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk vl x}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).append (.cons hurv rr))
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).append (.cons hulv rl))
  (hclassR : RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ur vr)
  (hclassL : RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ul vl) :
-- imply
  ∃ f g : Site 2, rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ (s(f, g) = s(ur, vr) ∨ (∃ (u' v' : Site 2) (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y u') (r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk v' vr) (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj u' v'), ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u' v' ∧ rr.reverse = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).append (.cons huv r) ∧ (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧ r.length < rr.length ∧ r.length + rl.length < rr.length + rl.length ∧ RlcTwoChannelFullPhysicalLeftArcClassifiedBad gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) u' v' ∧ RlcTwoChannelFullPhysicalWallTerminalProductClassification gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) (vr := vr) (vl := v') qr q ∧ RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) (vr := vr) (vl := v') qr q) ∨ s(f, g) = s(ul, vl) ∨ ∃ (u' v' : Site 2) (q : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x u') (r : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk v' vl) (huv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj u' v'), ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' u' v' ∧ rl.reverse = (q.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).append (.cons huv r) ∧ (s(f, g) = s(u', v') ∨ s(f, g) ∈ r.edges) ∧ r.length < rl.length ∧ rr.length + r.length < rr.length + rl.length ∧ RlcTwoChannelFullPhysicalRightArcClassifiedBad gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) u' v' ∧ RlcTwoChannelFullPhysicalWallTerminalProductClassification gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) (vr := v') (vl := vl) q ql ∧ RlcTwoChannelFullPhysicalLocalizedWallTerminalFamilyAlternative gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) (vr := v') (vl := vl) q ql) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_BChanging_terminal_or_strictSuffix hfaith A B hAright hAleft hBright hBleft hnoPair c hx hy hxPath hyPath qr rr ql rl hurv hulv hdecR hdecL hclassR hclassL

/--
[rlc_twoChannelFullPhysical_suffixPair_strongInduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_suffixPair_strongInduction_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (P : ∀ {a b c d : Site 2}, (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b → (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d → Prop)
  (hstep : ∀ {a b c d : Site 2} (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d), (∀ {a' b' c' d' : Site 2} (rr' : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a' b') (rl' : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c' d'), rr'.length + rl'.length < rr.length + rl.length → P rr' rl') → P rr rl) :
-- imply
  ∀ {a b c d : Site 2} (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d), P rr rl := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_suffixPair_strongInduction P hstep

/--
[rlc_twoChannelFullPhysical_candidateSuffix_lexStrongInduction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_candidateSuffix_lexStrongInduction_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
-- given
  (P : Nat → ∀ {a b c d : Site 2}, (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b → (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d → Prop)
  (hstep : ∀ (k : Nat) {a b c d : Site 2} (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d), (∀ (k' : Nat), k' < k → ∀ {a' b' c' d' : Site 2} (rr' : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a' b') (rl' : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c' d'), P k' rr' rl') → (∀ {a' b' c' d' : Site 2} (rr' : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a' b') (rl' : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c' d'), rr'.length + rl'.length < rr.length + rl.length → P k rr' rl') → P k rr rl) :
-- imply
  ∀ (k : Nat) {a b c d : Site 2} (rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk a b) (rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk c d), P k rr rl := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_candidateSuffix_lexStrongInduction P hstep

/--
[rlc_walkIndexInterval_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walkIndexInterval_support_eq
  {G : SimpleGraph V}
  {a b : V}
  {W : G.Walk a b}
  {i j : Nat}
  {v : V}
-- given
  (hi : i ≤ W.length)
  (hij : i ≤ j)
  (hj : j ≤ W.length)
  (hv : v ∈ (rlc_walkIndexInterval W i j hi hij hj).support) :
-- imply
  ∃ k : Nat, i ≤ k ∧ k ≤ j ∧ W.getVert k = v := by
-- proof
  apply StatMech.Universality.rlc_walkIndexInterval_support W i j hi hij hj hv

/--
[rlc_walkIndexInterval_getVert_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walkIndexInterval_getVert_mem_eq
  {G : SimpleGraph V}
  {a b : V}
  {W : G.Walk a b}
  {i j : Nat}
  {k : Nat}
-- given
  (hi : i ≤ W.length)
  (hij : i ≤ j)
  (hj : j ≤ W.length)
  (hik : i ≤ k)
  (hkj : k ≤ j) :
-- imply
  W.getVert k ∈ (rlc_walkIndexInterval W i j hi hij hj).support := by
-- proof
  apply StatMech.Universality.rlc_walkIndexInterval_getVert_mem W i j hi hij hj hik hkj

/--
[rlc_walkIndexInterval_support_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walkIndexInterval_support_interior_eq
  {G : SimpleGraph V}
  {a b : V}
  {W : G.Walk a b}
  {i j : Nat}
  {v : V}
-- given
  (hi : i ≤ W.length)
  (hij : i ≤ j)
  (hj : j ≤ W.length)
  (hv : v ∈ (rlc_walkIndexInterval W i j hi hij hj).support)
  (hvi : v ≠ W.getVert i)
  (hvj : v ≠ W.getVert j) :
-- imply
  ∃ k : Nat, i < k ∧ k < j ∧ W.getVert k = v := by
-- proof
  apply StatMech.Universality.rlc_walkIndexInterval_support_interior W i j hi hij hj hv hvi hvj

/--
[rlc_walk_ordered_to_complementary_crosscut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_ordered_to_complementary_crosscut_eq
  {G K : SimpleGraph (Site 2)}
  {u x y a b : Site 2}
  {c : G.Walk u u}
  {W : K.Walk a b}
-- given
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (ha : a ∈ (rlc_orderedContourArc c hx hy).support)
  (hb : b ∈ (rlc_complementaryContourArc c hx hy).support) :
-- imply
  (∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c hx hy).support ∧ z ∈ (rlc_complementaryContourArc c hx hy).support) ∨ ∃ (i j : Nat) (hi : i ≤ W.length) (hij : i ≤ j) (hj : j ≤ W.length), i < j ∧ W.getVert i ∈ (rlc_orderedContourArc c hx hy).support ∧ W.getVert j ∈ (rlc_complementaryContourArc c hx hy).support ∧ ∀ z ∈ (rlc_walkIndexInterval W i j hi hij hj).support, z = W.getVert i ∨ z = W.getVert j ∨ z ∉ c.support := by
-- proof
  apply StatMech.Universality.rlc_walk_ordered_to_complementary_crosscut c hx hy W ha hb

/--
[rlc_walk_exists_first_contact_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_exists_first_contact_after_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b u : V}
  {W : G.Walk a b}
  {C : G.Walk u u}
  {j : Nat}
-- given
  (hjLength : j < W.length)
  (hend : b ∈ C.support) :
-- imply
  ∃ j' : Nat, j < j' ∧ j' ≤ W.length ∧ W.getVert j' ∈ C.support ∧ ∀ l : Nat, j < l → l < j' → W.getVert l ∉ C.support := by
-- proof
  apply StatMech.Universality.rlc_walk_exists_first_contact_after W C hjLength hend

/--
[rlc_walk_contactInterval_same_leftRegion_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_contactInterval_same_leftRegion_side_eq
  {a b u : Site 2}
  {W : (hypercubicLattice 2).Walk a b}
  {C : (hypercubicLattice 2).Walk u u}
  {i k j : Nat}
-- given
  (hik : i < k)
  (hkj : k < j)
  (hjLength : j ≤ W.length)
  (hbetween : ∀ l : Nat, i < l → l < j → W.getVert l ∉ C.support)
  (hkOutside : W.getVert k ∉ jec_leftRegion C) :
-- imply
  ∀ l : Nat, i < l → l < j → W.getVert l ∉ jec_leftRegion C := by
-- proof
  apply StatMech.Universality.rlc_walk_contactInterval_same_leftRegion_side W C hik hkj hjLength hbetween hkOutside

/--
[rlc_walk_ordered_to_complementary_contactInterval_exteriorSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_ordered_to_complementary_contactInterval_exteriorSide_eq
  {G : SimpleGraph (Site 2)}
  {u x y a b : Site 2}
  {c : G.Walk u u}
  {W : (hypercubicLattice 2).Walk a b}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (ha : a ∈ (rlc_orderedContourArc c hx hy).support)
  (hb : b ∈ (rlc_complementaryContourArc c hx hy).support) :
-- imply
  (∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c hx hy).support ∧ z ∈ (rlc_complementaryContourArc c hx hy).support) ∨ ∃ i j : Nat, i < j ∧ j ≤ W.length ∧ W.getVert i ∈ (rlc_orderedContourArc c hx hy).support ∧ W.getVert j ∈ (rlc_complementaryContourArc c hx hy).support ∧ (∀ l : Nat, i < l → l < j → W.getVert l ∉ c.support) ∧ (j = i + 1 ∨ (i + 1 < j ∧ ∀ (_hfirstOutside : W.getVert (i + 1) ∉ jec_leftRegion (c.mapLe hG)) (l : Nat), i < l → l < j → W.getVert l ∉ jec_leftRegion (c.mapLe hG))) := by
-- proof
  apply StatMech.Universality.rlc_walk_ordered_to_complementary_contactInterval_exteriorSide hG c hx hy W ha hb

/--
[rlc_contactInterval_firstVertex_exterior_no_go](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_contactInterval_firstVertex_exterior_no_go_eq :
-- imply
  ∃ (c : (hypercubicLattice 2).Walk ![0, 0] ![0, 0]) (T : (hypercubicLattice 2).Walk ![2, 1] ![0, 1]), c.IsCycle ∧ T.getVert 0 ∈ c.support ∧ T.getVert 2 ∈ c.support ∧ (∀ l : Nat, 0 < l → l < 2 → T.getVert l ∉ c.support) ∧ T.getVert 1 ∈ jec_leftRegion c := by
-- proof
  apply StatMech.Universality.rlc_contactInterval_firstVertex_exterior_no_go

/--
[rlc_walk_takeUntil_append_of_notMem_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_takeUntil_append_of_notMem_left_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v w x : V}
  {p : G.Walk u v}
  {q : G.Walk v w}
-- given
  (hxP : x ∉ p.support)
  (hxQ : x ∈ q.support) :
-- imply
  (p.append q).takeUntil x (SimpleGraph.Walk.subset_support_append_right p q hxQ) = p.append (q.takeUntil x hxQ) := by
-- proof
  apply StatMech.Universality.rlc_walk_takeUntil_append_of_notMem_left p q hxP hxQ

/--
[rlc_list_idxOf_map_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_list_idxOf_map_of_injective_eq
  [DecidableEq A]
  [DecidableEq B]
  {f : A → B}
  {l : List A}
  {x : A}
-- given
  (hf : Function.Injective f) :
-- imply
  (l.map f).idxOf (f x) = l.idxOf x := by
-- proof
  apply StatMech.Universality.rlc_list_idxOf_map_of_injective f hf l x

/--
[rlc_list_idxOf_drop_idxOf_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_list_idxOf_drop_idxOf_of_le_eq
  [DecidableEq A]
  {l : List A}
  {a b : A}
-- given
  (hnodup : l.Nodup)
  (ha : a ∈ l)
  (hb : b ∈ l)
  (hab : l.idxOf a ≤ l.idxOf b) :
-- imply
  (l.drop (l.idxOf a)).idxOf b = l.idxOf b - l.idxOf a := by
-- proof
  apply StatMech.Universality.rlc_list_idxOf_drop_idxOf_of_le l hnodup ha hb hab

/--
[rlc_isPath_dropUntil_dropUntil_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_isPath_dropUntil_dropUntil_eq_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v a b : V}
  {W : G.Walk u v}
-- given
  (hW : W.IsPath)
  (ha : a ∈ W.support)
  (hb : b ∈ W.support)
  (hab : W.support.idxOf a ≤ W.support.idxOf b)
  (hbSuffix : b ∈ (W.dropUntil a ha).support) :
-- imply
  (W.dropUntil a ha).dropUntil b hbSuffix = W.dropUntil b hb := by
-- proof
  apply StatMech.Universality.rlc_isPath_dropUntil_dropUntil_eq W hW ha hb hab hbSuffix

/--
[rlc_isPath_takeUntil_dropUntil_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_isPath_takeUntil_dropUntil_contact_eq
  {G : SimpleGraph (Site 2)}
  {u w a b v : Site 2}
  {W : G.Walk u w}
-- given
  (hW : W.IsPath)
  (ha : a ∈ W.support)
  (hb : b ∈ W.support)
  (hab : W.support.idxOf a ≤ W.support.idxOf b)
  (hvPrefix : v ∈ (W.takeUntil a ha).support)
  (hvSuffix : v ∈ (W.dropUntil b hb).support) :
-- imply
  v = a ∧ a = b := by
-- proof
  apply StatMech.Universality.rlc_isPath_takeUntil_dropUntil_contact W hW ha hb hab hvPrefix hvSuffix

/--
[rlc_isPath_idxOf_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_isPath_idxOf_end_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u w : V}
  {W : G.Walk u w}
-- given
  (hW : W.IsPath) :
-- imply
  W.support.idxOf w = W.length := by
-- proof
  apply StatMech.Universality.rlc_isPath_idxOf_end W hW

/--
[rlc_isPath_idxOf_getVert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_isPath_idxOf_getVert_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {W : G.Walk u v}
  {i : Nat}
-- given
  (hW : W.IsPath)
  (hi : i ≤ W.length) :
-- imply
  W.support.idxOf (W.getVert i) = i := by
-- proof
  apply StatMech.Universality.rlc_isPath_idxOf_getVert W hW i hi

/--
[rlc_walk_idxOf_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_idxOf_start_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u w : V}
  {W : G.Walk u w} :
-- imply
  W.support.idxOf u = 0 := by
-- proof
  apply StatMech.Universality.rlc_walk_idxOf_start W

/--
[rlc_bookExteriorEndpointDetour_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookExteriorEndpointDetour_mem_rect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {v : Site 2}
-- given
  (hv : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support) :
-- imply
  v ∈ rect (-2 * n - 2) (2 * n + 2) (-n) (n + 2) := by
-- proof
  apply StatMech.Universality.rlc_bookExteriorEndpointDetour_mem_rect gamma gamma' hv

/--
[rlc_bookExteriorEndpointDetour_topRight_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookExteriorEndpointDetour_topRight_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  (![(2 * n + 2), n + 2] : Site 2) ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support := by
-- proof
  apply StatMech.Universality.rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma'

/--
[rlc_bookExteriorEndpointDetour_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookExteriorEndpointDetour_support_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {v : Site 2}
-- given
  (hv : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support) :
-- imply
  v ∈ (sw_horizSeg ((gamma.1.2.1 : Site 2) 1) ((gamma.1.2.1 : Site 2) 0) (2 * n + 2)).support ∨ v ∈ (sw_vertSeg (2 * n + 2) ((gamma.1.2.1 : Site 2) 1) (n + 2)).support ∨ v ∈ (sw_horizSeg (n + 2) (2 * n + 2) (-2 * n - 2)).support ∨ v ∈ (sw_horizSeg ((gamma'.1.1 : Site 2) 1) ((gamma'.1.1 : Site 2) 0) (-2 * n - 2)).support ∨ v ∈ (sw_vertSeg (-2 * n - 2) ((gamma'.1.1 : Site 2) 1) (n + 2)).support := by
-- proof
  apply StatMech.Universality.rlc_bookExteriorEndpointDetour_support_cases gamma gamma' hv

/--
[rlc_sw_lshape_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_sw_lshape_isPath_eq
  {x0 y0 x1 y1 : Int} :
-- imply
  (sw_lshape x0 y0 x1 y1).IsPath := by
-- proof
  apply StatMech.Universality.rlc_sw_lshape_isPath x0 y0 x1 y1

/--
[rlc_bookExteriorEndpointDetour_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookExteriorEndpointDetour_isPath_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hn : 0 < n) :
-- imply
  (rlc_bookExteriorEndpointDetour gamma gamma').IsPath := by
-- proof
  apply StatMech.Universality.rlc_bookExteriorEndpointDetour_isPath hn gamma gamma'

/--
[rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hvDetour : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support)
  (hvBox : v ∈ rect 0 (2 * n) (-n) n) :
-- imply
  v = (gamma.1.2.1 : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookExteriorEndpointDetour_meets_rightBox_only_endpoint hn gamma gamma' hvDetour hvBox

/--
[rlc_bookExteriorEndpointDetour_meets_leftBox_only_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookExteriorEndpointDetour_meets_leftBox_only_endpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hvDetour : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support)
  (hvBox : v ∈ rect (-2 * n) 0 (-n) n) :
-- imply
  v = (gamma'.1.1 : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookExteriorEndpointDetour_meets_leftBox_only_endpoint hn gamma gamma' hvDetour hvBox

/--
[rlc_bookTraceNetworkBracket_eq_simple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookTraceNetworkBracket_eq_simple_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
-- given
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
-- imply
  rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs = rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft := by
-- proof
  apply StatMech.Universality.rlc_bookTraceNetworkBracket_eq_simple hr hs hsLeft hrs

/--
[rlc_bookPhysicalTraceNetworkBracket_eq_simple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_eq_simple_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
-- given
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
-- imply
  rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs = rlc_bookSimplePhysicalTraceNetworkBracket gamma gamma' hr hsLeft := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_eq_simple hr hs hsLeft hrs

/--
[rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
-- given
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
-- imply
  (![(2 * n + 2), n + 2] : Site 2) ∈ (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support := by
-- proof
  apply StatMech.Universality.rlc_bookSimpleTraceNetworkBracket_exteriorPoint_mem gamma gamma' hr hsLeft

/--
[rlc_bookSimpleTraceNetworkBracket_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookSimpleTraceNetworkBracket_isPath_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
-- imply
  (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).IsPath := by
-- proof
  apply StatMech.Universality.rlc_bookSimpleTraceNetworkBracket_isPath hn hfaith hr hsLeft

/--
[rlc_bookSimplePhysicalTraceNetworkBracket_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookSimplePhysicalTraceNetworkBracket_isPath_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) :
-- imply
  (rlc_bookSimplePhysicalTraceNetworkBracket gamma gamma' hr hsLeft).IsPath := by
-- proof
  apply StatMech.Universality.rlc_bookSimplePhysicalTraceNetworkBracket_isPath hn hfaith hr hsLeft

/--
[rlc_bookPhysicalTraceNetworkBracket_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_isPath_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
-- imply
  (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).IsPath := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_isPath hn hfaith hr hs hsLeft hrs

/--
[rlc_bookPhysicalTraceNetworkBracket_sameContact_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_sameContact_isPath_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1) :
-- imply
  (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hr hrLeft le_rfl).IsPath := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_sameContact_isPath hn hfaith hr hrLeft

/--
[rlc_bookPhysicalTraceNetworkBracket_sameContact_right_index_le_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_sameContact_right_index_le_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r : Site 2}
  {j : Nat}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1)
  (hjLength : j ≤ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hr hrLeft le_rfl).length)
  (hjRight : rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hr hrLeft le_rfl).getVert j) ∈ rlc_pathVertices gamma.1) :
-- imply
  j ≤ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hr hrLeft le_rfl).support.idxOf (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_sameContact_right_index_le_exterior hn hfaith hr hrLeft hjLength hjRight

/--
[rlc_bookSimpleTraceNetworkBracket_right_mem_exteriorPrefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookSimpleTraceNetworkBracket_right_mem_exteriorPrefix_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s w : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hw : w ∈ (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support)
  (hwRight : w ∈ rlc_pathVertices gamma.1) :
-- imply
  let d : Site 2 := ![2 * n + 2, n + 2] let W := rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft ∀ hd : d ∈ W.support, w ∈ (W.takeUntil d hd).support := by
-- proof
  apply StatMech.Universality.rlc_bookSimpleTraceNetworkBracket_right_mem_exteriorPrefix hn hfaith hr hsLeft hw hwRight

/--
[rlc_bookPhysicalTraceNetworkBracket_right_index_le_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_right_index_le_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
  {j : Nat}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hjLength : j ≤ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).length)
  (hjRight : rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) ∈ rlc_pathVertices gamma.1) :
-- imply
  j ≤ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support.idxOf (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_right_index_le_exterior hn hfaith hr hs hsLeft hrs hjLength hjRight

/--
[rlc_bookPhysicalExteriorEndpointDetour_meets_filledBoundary_only_endpointCollar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalExteriorEndpointDetour_meets_filledBoundary_only_endpointCollar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hvDetour : v ∈ ((rlc_bookExteriorEndpointDetour gamma gamma').map rlc_dualReflectSymmLatticeHom).support)
  (hvBoundary : v ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  v = rlc_dualReflect.symm (gamma.1.2.1 : Site 2) ∨ v = rlc_dualReflect.symm (gamma'.1.1 : Site 2) ∨ v = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalExteriorEndpointDetour_meets_filledBoundary_only_endpointCollar hn gamma gamma' omega hvDetour hvBoundary

/--
[rlc_bookPhysicalRightEndpointLeg_meets_filledBoundary_only_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalRightEndpointLeg_meets_filledBoundary_only_endpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {w : Site 2}
-- given
  (hn : 0 < n)
  (hw : w ∈ (sw_lshape ((gamma.1.2.1 : Site 2) 0) ((gamma.1.2.1 : Site 2) 1) (2 * n + 2) (n + 2)).support)
  (hwBoundary : rlc_dualReflect.symm w ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  w = (gamma.1.2.1 : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalRightEndpointLeg_meets_filledBoundary_only_endpoint hn gamma gamma' omega hw hwBoundary

/--
[rlc_bookSimplePhysicalTraceNetworkBracket_boundaryContact_provenance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookSimplePhysicalTraceNetworkBracket_boundaryContact_provenance_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s v : Site 2}
-- given
  (hn : 0 < n)
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hvBracket : v ∈ (rlc_bookSimplePhysicalTraceNetworkBracket gamma gamma' hr hsLeft).support)
  (hvBoundary : v ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨ v = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookSimplePhysicalTraceNetworkBracket_boundaryContact_provenance hn gamma gamma' omega hr hsLeft hvBracket hvBoundary

/--
[rlc_bookExteriorEndpointDetour_meets_rightTrace_only_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookExteriorEndpointDetour_meets_rightTrace_only_endpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hvDetour : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support)
  (hvRight : v ∈ rlc_pathVertices gamma.1) :
-- imply
  v = (gamma.1.2.1 : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookExteriorEndpointDetour_meets_rightTrace_only_endpoint hfaith hvDetour hvRight

/--
[rlc_bookExteriorEndpointDetour_meets_leftTrace_only_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookExteriorEndpointDetour_meets_leftTrace_only_endpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hvDetour : v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support)
  (hvLeft : v ∈ rlc_pathVertices gamma'.1) :
-- imply
  v = (gamma'.1.1 : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookExteriorEndpointDetour_meets_leftTrace_only_endpoint hfaith hvDetour hvLeft

/--
[rlc_bookOuterTraceNetworkArc_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookOuterTraceNetworkArc_support_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {s v : Site 2}
-- given
  (hsRight : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hv : v ∈ (rlc_bookOuterTraceNetworkArc gamma gamma' hsRight hsLeft).support) :
-- imply
  v ∈ ((rlc_ambientCrossingWalk gamma.1).dropUntil s ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 s).2 hsRight)).support ∨ v ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support ∨ v ∈ ((rlc_ambientCrossingWalk gamma'.1).takeUntil (rlc_flipX s) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_flipX s)).2 hsLeft)).support := by
-- proof
  apply StatMech.Universality.rlc_bookOuterTraceNetworkArc_support_cases gamma gamma' hsRight hsLeft hv

/--
[rlc_rightAmbientTraceCanonicalSegment_support_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_rightAmbientTraceCanonicalSegment_support_path_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {r s v : Site 2}
-- given
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hv : v ∈ (rlc_rightAmbientTraceCanonicalSegment gamma hr hs hrs).support) :
-- imply
  v ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_rightAmbientTraceCanonicalSegment_support_path gamma hr hs hrs hv

/--
[rlc_bookPhysicalTraceNetworkBracket_boundaryContact_provenance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_boundaryContact_provenance_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s v : Site 2}
-- given
  (hn : 0 < n)
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hvBracket : v ∈ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support)
  (hvBoundary : v ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨ v = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_boundaryContact_provenance hn gamma gamma' omega hr hs hsLeft hrs hvBracket hvBoundary

/--
[rlc_bookTraceNetworkBracket_meets_rightPrefix_only_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookTraceNetworkBracket_meets_rightPrefix_only_start_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hvBracket : v ∈ (rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support)
  (hvPrefix : v ∈ ((rlc_ambientCrossingWalk gamma.1).takeUntil r ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr)).support) :
-- imply
  v = r := by
-- proof
  apply StatMech.Universality.rlc_bookTraceNetworkBracket_meets_rightPrefix_only_start hfaith hr hs hsLeft hrs hvBracket hvPrefix

/--
[rlc_bookTraceNetworkBracket_meets_leftSuffix_only_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookTraceNetworkBracket_meets_leftSuffix_only_end_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hvBracket : v ∈ (rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support)
  (hvSuffix : v ∈ ((rlc_ambientCrossingWalk gamma'.1).dropUntil (rlc_flipX s) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_flipX s)).2 hsLeft)).support) :
-- imply
  v = rlc_flipX s := by
-- proof
  apply StatMech.Universality.rlc_bookTraceNetworkBracket_meets_leftSuffix_only_end hfaith hr hs hsLeft hrs hvBracket hvSuffix

/--
[rlc_bookPhysicalTraceNetworkBracket_meets_rightPrefix_only_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_meets_rightPrefix_only_start_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hvBracket : v ∈ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support)
  (hvPrefix : v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil r ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr)).map rlc_dualReflectSymmLatticeHom).support) :
-- imply
  v = rlc_dualReflect.symm r := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_meets_rightPrefix_only_start hfaith hr hs hsLeft hrs hvBracket hvPrefix

/--
[rlc_bookPhysicalTraceNetworkBracket_axisSource_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_axisSource_not_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hrAxis : r ≠ (gamma.1.1 : Site 2)) :
-- imply
  phb_doubleDualShift (gamma.1.1 : Site 2) ∉ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_axisSource_not_mem hfaith hr hs hsLeft hrs hrAxis

/--
[rlc_bookPhysicalTraceNetworkBracket_meets_leftSuffix_only_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_meets_leftSuffix_only_end_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hvBracket : v ∈ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support)
  (hvSuffix : v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil (rlc_flipX s) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_flipX s)).2 hsLeft)).map rlc_dualReflectSymmLatticeHom).support) :
-- imply
  v = rlc_dualReflect.symm (rlc_flipX s) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_meets_leftSuffix_only_end hfaith hr hs hsLeft hrs hvBracket hvSuffix

/--
[rlc_bookPhysicalTraceNetworkBracket_meets_sourceTraceCollars_only_ends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_meets_sourceTraceCollars_only_ends_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hvBracket : v ∈ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support)
  (hvCollar : v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil r ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 r).2 hr)).map rlc_dualReflectSymmLatticeHom).support ∨ v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil (rlc_flipX s) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_flipX s)).2 hsLeft)).map rlc_dualReflectSymmLatticeHom).support) :
-- imply
  v = rlc_dualReflect.symm r ∨ v = rlc_dualReflect.symm (rlc_flipX s) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_meets_sourceTraceCollars_only_ends hfaith hr hs hsLeft hrs hvBracket hvCollar

/--
[rlc_bookPhysicalTraceNetworkBracket_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_mem_rect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s v : Site 2}
-- given
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hv : v ∈ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support) :
-- imply
  v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_mem_rect gamma gamma' hr hs hsLeft hrs hv

/--
[rlc_bookPhysicalTraceNetworkBracket_exteriorPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_exteriorPoint_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
-- given
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s) :
-- imply
  rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_exteriorPoint_mem gamma gamma' hr hs hsLeft hrs

/--
[rlc_bookTraceNetworkBracket_prefix_exterior_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookTraceNetworkBracket_prefix_exterior_support_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s v : Site 2}
-- given
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hd : (![(2 * n + 2), n + 2] : Site 2) ∈ (rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support)
  (hv : v ∈ ((rlc_bookTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).takeUntil (![(2 * n + 2), n + 2] : Site 2) hd).support) :
-- imply
  v ∈ rlc_pathVertices gamma.1 ∨ v ∈ (sw_lshape ((gamma.1.2.1 : Site 2) 0) ((gamma.1.2.1 : Site 2) 1) (2 * n + 2) (n + 2)).support := by
-- proof
  apply StatMech.Universality.rlc_bookTraceNetworkBracket_prefix_exterior_support_cases gamma gamma' hr hs hsLeft hrs hd hv

/--
[rlc_bookPhysicalTraceNetworkBracket_beforeExterior_boundaryContact_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_beforeExterior_boundaryContact_right_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s : Site 2}
  {k : Nat}
-- given
  (hn : 0 < n)
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hk : k < (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support.idxOf (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)))
  (hkBoundary : (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert k ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert k) ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_beforeExterior_boundaryContact_right hn gamma gamma' omega hr hs hsLeft hrs hk hkBoundary

/--
[rlc_bookPhysicalTraceNetworkBracket_contactExtrema](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_contactExtrema_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hcycle : c.IsCycle)
  (hstart : rlc_dualReflect.symm r ∈ c.support)
  (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
-- imply
  let B := rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) let k := B.support.idxOf d ∃ i j : Nat, i < k ∧ k < j ∧ j ≤ B.length ∧ B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧ B.getVert k = d ∧ (∀ l : Nat, i < l → l < j → B.getVert l ∉ c.support) ∧ (∀ l : Nat, i < l → l < j → B.getVert l ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧ rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧ (rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma'.1 ∨ B.getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_contactExtrema hn gamma gamma' omega hr hs hsLeft hrs c hcycle hstart hend

/--
[rlc_bookPhysicalTraceNetworkBracket_ordered_contactExtrema](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_ordered_contactExtrema_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hcycle : c.IsCycle)
  (hstart : rlc_dualReflect.symm r ∈ c.support)
  (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
-- imply
  let B := rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) let k := B.support.idxOf d ∃ i j : Nat, i < k ∧ k < j ∧ j ≤ B.length ∧ B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧ B.getVert k = d ∧ (∀ l : Nat, i < l → l < j → B.getVert l ∉ c.support) ∧ (∀ l : Nat, i < l → l < j → B.getVert l ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧ rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧ (rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma'.1 ∨ B.getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_ordered_contactExtrema hn gamma gamma' hfaith omega hr hs hsLeft hrs c hcycle hstart hend

/--
[rlc_bookPhysicalTraceNetworkBracket_next_left_after_collar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_next_left_after_collar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {j : Nat}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hcycle : c.IsCycle)
  (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support)
  (hjLength : j ≤ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).length)
  (hkltj : (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support.idxOf (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) < j)
  (hjCollar : (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
-- imply
  ∃ j' : Nat, j < j' ∧ j' ≤ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).length ∧ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j' ∈ c.support ∧ rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j') ∈ rlc_pathVertices gamma'.1 ∧ ∀ l : Nat, j < l → l < j' → (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert l ∉ c.support := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_next_left_after_collar hn gamma gamma' hfaith omega hr hs hsLeft hrs c hcycle hend hjLength hkltj hjCollar

/--
[rlc_path_edges_disjoint_of_endpoint_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_path_edges_disjoint_of_endpoint_intersection_eq
  {G : SimpleGraph V}
  {u v d : V}
  {p : G.Walk u v}
  {q : G.Walk v u}
-- given
  (hp : p.IsPath)
  (hd : d ∈ p.support)
  (hdu : d ≠ u)
  (hdv : d ≠ v)
  (hinter : ∀ x, x ∈ p.support → x ∈ q.support → x = u ∨ x = v) :
-- imply
  p.edges.Disjoint q.edges := by
-- proof
  apply StatMech.Universality.rlc_path_edges_disjoint_of_endpoint_intersection hp hd hdu hdv hinter

/--
[rlc_exteriorChord_complementaryArcCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_complementaryArcCycles_eq
  {H K : SimpleGraph (Site 2)}
  {u a b d : Site 2}
  {c : H.Walk u u}
  {p : K.Walk a b}
-- given
  (hHK : H ≤ K)
  (hc : c.IsCycle)
  (hp : p.IsPath)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hdp : d ∈ p.support)
  (hdc : d ∉ c.support)
  (hclean : ∀ x ∈ p.support, x = a ∨ x = b ∨ x ∉ c.support) :
-- imply
  (p.append ((rlc_orderedContourArc c ha hb).mapLe hHK).reverse).IsCycle ∧ (p.append ((rlc_complementaryContourArc c ha hb).mapLe hHK).reverse).IsCycle := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_complementaryArcCycles hHK c hc p hp ha hb hdp hdc hclean

/--
[rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff_eq
  {a f g p q : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
-- given
  (hnd : C.edges.Nodup)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hshared : sharedPrimalEdge f g = s(p, q)) :
-- imply
  rlc_OppositeLoopSides C p q ↔ s(f, g) ∈ C.edges := by
-- proof
  apply StatMech.Universality.rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff C hnd hfg hpq hshared

/--
[rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff_oddCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff_oddCount_eq
  {a f g p q : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hshared : sharedPrimalEdge f g = s(p, q)) :
-- imply
  rlc_OppositeLoopSides C p q ↔ Odd (C.edges.count s(f, g)) := by
-- proof
  apply StatMech.Universality.rlc_sharedPrimalEdge_flanks_oppositeLoopSides_iff_oddCount C hfg hpq hshared

/--
[rlc_two_terminalFlanks_oppositeLoopSides_of_countParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_two_terminalFlanks_oppositeLoopSides_of_countParity_eq
  {a f g f' g' p q p' q' : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
  {Q : (hypercubicLattice 2).Walk q q'}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfg' : (hypercubicLattice 2).Adj f' g')
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hshared' : sharedPrimalEdge f' g' = s(p', q'))
  (hQoff : ∀ z ∈ Q.support, z ∉ C.support)
  (hRodd : Odd (C.edges.count s(f, g)))
  (hLeven : Even (C.edges.count s(f', g'))) :
-- imply
  rlc_OppositeLoopSides C p p' := by
-- proof
  apply StatMech.Universality.rlc_two_terminalFlanks_oppositeLoopSides_of_countParity C hfg hfg' hpq hpq' hshared hshared' Q hQoff hRodd hLeven

/--
[rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_orderedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_orderedArc_eq
  {G : SimpleGraph (Site 2)}
  {u x y f g f' g' p q p' q' : Site 2}
  {c : G.Walk u u}
  {B : (hypercubicLattice 2).Walk x y}
  {Q : (hypercubicLattice 2).Walk q q'}
  {W : (hypercubicLattice 2).Walk p p'}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hR : s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hL : s(f', g') ∈ (rlc_complementaryContourArc c hx hy).edges)
  (hfB : f ∉ B.support)
  (hf'B : f' ∉ B.support)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfg' : (hypercubicLattice 2).Adj f' g')
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hshared' : sharedPrimalEdge f' g' = s(p', q'))
  (hQW : Q.support ⊆ W.support) :
-- imply
  (∃ z ∈ W.support, z ∈ B.support) ∨ ∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c hx hy).support := by
-- proof
  apply StatMech.Universality.rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_orderedArc hG c hc hx hy B hR hL hfB hf'B hfg hfg' hpq hpq' hshared hshared' Q W hQW

/--
[rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_complementaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_complementaryArc_eq
  {G : SimpleGraph (Site 2)}
  {u x y f g f' g' p q p' q' : Site 2}
  {c : G.Walk u u}
  {B : (hypercubicLattice 2).Walk x y}
  {Q : (hypercubicLattice 2).Walk q q'}
  {W : (hypercubicLattice 2).Walk p p'}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hR : s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hL : s(f', g') ∈ (rlc_complementaryContourArc c hx hy).edges)
  (hfB : f ∉ B.support)
  (hf'B : f' ∉ B.support)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfg' : (hypercubicLattice 2).Adj f' g')
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hshared' : sharedPrimalEdge f' g' = s(p', q'))
  (hQW : Q.support ⊆ W.support) :
-- imply
  (∃ z ∈ W.support, z ∈ B.support) ∨ ∃ z ∈ W.support, z ∈ (rlc_complementaryContourArc c hx hy).support := by
-- proof
  apply StatMech.Universality.rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_complementaryArc hG c hc hx hy B hR hL hfB hf'B hfg hfg' hpq hpq' hshared hshared' Q W hQW

/--
[rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_bothArcs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_bothArcs_eq
  {G : SimpleGraph (Site 2)}
  {u x y f g f' g' p q p' q' : Site 2}
  {c : G.Walk u u}
  {B : (hypercubicLattice 2).Walk x y}
  {Q : (hypercubicLattice 2).Walk q q'}
  {W : (hypercubicLattice 2).Walk p p'}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hR : s(f, g) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hL : s(f', g') ∈ (rlc_complementaryContourArc c hx hy).edges)
  (hfB : f ∉ B.support)
  (hf'B : f' ∉ B.support)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfg' : (hypercubicLattice 2).Adj f' g')
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hshared' : sharedPrimalEdge f' g' = s(p', q'))
  (hQW : Q.support ⊆ W.support) :
-- imply
  (∃ z ∈ W.support, z ∈ B.support) ∨ ((∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c hx hy).support) ∧ ∃ z ∈ W.support, z ∈ (rlc_complementaryContourArc c hx hy).support) := by
-- proof
  apply StatMech.Universality.rlc_exteriorBracket_terminalFlankWalk_meets_bracket_or_bothArcs hG c hc hx hy B hR hL hfB hf'B hfg hfg' hpq hpq' hshared hshared' Q W hQW

/--
[rlc_two_terminalFlanks_oppositeLoopSides_of_edgeXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_two_terminalFlanks_oppositeLoopSides_of_edgeXor_eq
  {a f g f' g' p q p' q' : Site 2}
  {C : (hypercubicLattice 2).Walk a a}
  {Q : (hypercubicLattice 2).Walk q q'}
-- given
  (hnd : C.edges.Nodup)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfg' : (hypercubicLattice 2).Adj f' g')
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hshared' : sharedPrimalEdge f' g' = s(p', q'))
  (hQoff : ∀ z ∈ Q.support, z ∉ C.support)
  (hedges : (s(f, g) ∈ C.edges ∧ s(f', g') ∉ C.edges) ∨ (s(f, g) ∉ C.edges ∧ s(f', g') ∈ C.edges)) :
-- imply
  rlc_OppositeLoopSides C p p' := by
-- proof
  apply StatMech.Universality.rlc_two_terminalFlanks_oppositeLoopSides_of_edgeXor C hnd hfg hfg' hpq hpq' hshared hshared' Q hQoff hedges

/--
[rlc_cleanChord_contourEdge_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_cleanChord_contourEdge_not_mem_eq
  {G : SimpleGraph (Site 2)}
  {u a b f g : Site 2}
  {c : G.Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hclean : ∀ z ∈ H.support, z = a ∨ z = b ∨ z ∉ c.support)
  (hfgC : s(f, g) ∈ c.edges)
  (hfa : f ≠ a)
  (hfb : f ≠ b) :
-- imply
  s(f, g) ∉ H.edges := by
-- proof
  apply StatMech.Universality.rlc_cleanChord_contourEdge_not_mem c H hclean hfgC hfa hfb

/--
[rlc_exteriorChord_terminalEdges_closureXor_of_arcPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_terminalEdges_closureXor_of_arcPlacement_eq
  {G : SimpleGraph (Site 2)}
  {u a b f g f' g' : Site 2}
  {c : G.Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (hc : c.IsTrail)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hR : s(f, g) ∈ (rlc_orderedContourArc c ha hb).edges)
  (hL : s(f', g') ∈ (rlc_complementaryContourArc c ha hb).edges)
  (hRH : s(f, g) ∉ H.edges)
  (hLH : s(f', g') ∉ H.edges) :
-- imply
  (s(f, g) ∈ (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).edges ∧ s(f', g') ∉ (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).edges) ∧ (s(f, g) ∉ (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse).edges ∧ s(f', g') ∈ (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse).edges) := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_terminalEdges_closureXor_of_arcPlacement hG c hc ha hb H hR hL hRH hLH

/--
[rlc_exteriorChord_rayCount_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_rayCount_sum_eq
  {G : SimpleGraph (Site 2)}
  {u a b : Site 2}
  {c : G.Walk u u}
  {p : (hypercubicLattice 2).Walk a b}
  {z : Site 2}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support) :
-- imply
  jec_rayCount z (p.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse) + jec_rayCount z (p.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse) = 2 * jec_rayCount z p + jec_rayCount z (c.mapLe hG) := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_rayCount_sum hG c ha hb p z

/--
[rlc_exteriorChord_leftRegion_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_leftRegion_xor_eq
  {G : SimpleGraph (Site 2)}
  {u a b : Site 2}
  {c : G.Walk u u}
  {p : (hypercubicLattice 2).Walk a b}
  {z : Site 2}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support) :
-- imply
  z ∈ jec_leftRegion (c.mapLe hG) ↔ (z ∈ jec_leftRegion (p.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse) ↔ z ∉ jec_leftRegion (p.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse)) := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_leftRegion_xor hG c ha hb p z

/--
[rlc_exteriorChord_one_closure_separates_inside_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_one_closure_separates_inside_outside_eq
  {G : SimpleGraph (Site 2)}
  {u a b x y : Site 2}
  {c : G.Walk u u}
  {p : (hypercubicLattice 2).Walk a b}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hx : x ∈ jec_leftRegion (c.mapLe hG))
  (hy : y ∉ jec_leftRegion (c.mapLe hG)) :
-- imply
  rlc_OppositeLoopSides (p.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse) x y ∨ rlc_OppositeLoopSides (p.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse) x y := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_one_closure_separates_inside_outside hG c ha hb p hx hy

/--
[rlc_exteriorChord_path_meets_chord_or_orderedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_path_meets_chord_or_orderedArc_eq
  {G : SimpleGraph (Site 2)}
  {u a b x y : Site 2}
  {c : G.Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hopp : rlc_OppositeLoopSides (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse) x y) :
-- imply
  ∃ z ∈ w.support, z ∈ H.support ∨ z ∈ (rlc_orderedContourArc c ha hb).support := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_path_meets_chord_or_orderedArc hG c ha hb H w hopp

/--
[rlc_exteriorChord_path_meets_chord_or_complementaryArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_path_meets_chord_or_complementaryArc_eq
  {G : SimpleGraph (Site 2)}
  {u a b x y : Site 2}
  {c : G.Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hopp : rlc_OppositeLoopSides (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse) x y) :
-- imply
  ∃ z ∈ w.support, z ∈ H.support ∨ z ∈ (rlc_complementaryContourArc c ha hb).support := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_path_meets_chord_or_complementaryArc hG c ha hb H w hopp

/--
[rlc_exteriorChord_path_meets_chord_of_separatingClosure_avoidance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_path_meets_chord_of_separatingClosure_avoidance_eq
  {G : SimpleGraph (Site 2)}
  {u a b x y : Site 2}
  {c : G.Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hsep : (rlc_OppositeLoopSides (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse) x y ∧ ∀ z ∈ w.support, z ∉ (rlc_orderedContourArc c ha hb).support) ∨ (rlc_OppositeLoopSides (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse) x y ∧ ∀ z ∈ w.support, z ∉ (rlc_complementaryContourArc c ha hb).support)) :
-- imply
  ∃ z ∈ w.support, z ∈ H.support := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_path_meets_chord_of_separatingClosure_avoidance hG c ha hb H w hsep

/--
[rlc_exteriorChord_terminalFlankPath_meets_chord_of_closureEdgeXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_terminalFlankPath_meets_chord_of_closureEdgeXor_eq
  {G : SimpleGraph (Site 2)}
  {u a b f g f' g' p q p' q' : Site 2}
  {c : G.Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {Q : (hypercubicLattice 2).Walk q q'}
  {W : (hypercubicLattice 2).Walk p p'}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfg' : (hypercubicLattice 2).Adj f' g')
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hshared : sharedPrimalEdge f g = s(p, q))
  (hshared' : sharedPrimalEdge f' g' = s(p', q'))
  (hQW : Q.support ⊆ W.support)
  (hselected : ((H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).IsCycle ∧ ((s(f, g) ∈ (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).edges ∧ s(f', g') ∉ (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).edges) ∨ (s(f, g) ∉ (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).edges ∧ s(f', g') ∈ (H.append ((rlc_orderedContourArc c ha hb).mapLe hG).reverse).edges)) ∧ ∀ z ∈ W.support, z ∉ (rlc_orderedContourArc c ha hb).support) ∨ ((H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse).IsCycle ∧ ((s(f, g) ∈ (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse).edges ∧ s(f', g') ∉ (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse).edges) ∨ (s(f, g) ∉ (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse).edges ∧ s(f', g') ∈ (H.append ((rlc_complementaryContourArc c ha hb).mapLe hG).reverse).edges)) ∧ ∀ z ∈ W.support, z ∉ (rlc_complementaryContourArc c ha hb).support)) :
-- imply
  ∃ z ∈ W.support, z ∈ H.support := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_terminalFlankPath_meets_chord_of_closureEdgeXor hG c ha hb H hfg hfg' hpq hpq' hshared hshared' Q W hQW hselected

/--
[rlc_exteriorChord_inside_to_outside_path_meets_chord_or_cycleArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_inside_to_outside_path_meets_chord_or_cycleArc_eq
  {G : SimpleGraph (Site 2)}
  {u a b x y : Site 2}
  {c : G.Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hx : x ∈ jec_leftRegion (c.mapLe hG))
  (hy : y ∉ jec_leftRegion (c.mapLe hG)) :
-- imply
  (∃ z ∈ w.support, z ∈ H.support ∨ z ∈ (rlc_orderedContourArc c ha hb).support) ∨ ∃ z ∈ w.support, z ∈ H.support ∨ z ∈ (rlc_complementaryContourArc c ha hb).support := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_inside_to_outside_path_meets_chord_or_cycleArc hG c ha hb H w hx hy

/--
[rlc_exteriorChord_inside_to_outside_path_meets_chord_of_avoids_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorChord_inside_to_outside_path_meets_chord_of_avoids_cycle_eq
  {G : SimpleGraph (Site 2)}
  {u a b x y : Site 2}
  {c : G.Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hx : x ∈ jec_leftRegion (c.mapLe hG))
  (hy : y ∉ jec_leftRegion (c.mapLe hG))
  (havoid : ∀ z ∈ w.support, z ∉ c.support) :
-- imply
  ∃ z ∈ w.support, z ∈ H.support := by
-- proof
  apply StatMech.Universality.rlc_exteriorChord_inside_to_outside_path_meets_chord_of_avoids_cycle hG c ha hb H w hx hy havoid

/--
[rlc_twoChannelFullPhysical_insideOutsideEdge_meets_exteriorChord_or_cycleArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_insideOutsideEdge_meets_exteriorChord_or_cycleArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  (∃ z ∈ hpq.toWalk.support, z ∈ H.support ∨ z ∈ (rlc_orderedContourArc c ha hb).support) ∨ ∃ z ∈ hpq.toWalk.support, z ∈ H.support ∨ z ∈ (rlc_complementaryContourArc c ha hb).support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_insideOutsideEdge_meets_exteriorChord_or_cycleArc c hcycle ha hb H hpq hpReach hqOut

/--
[rlc_twoChannelFullPhysical_insideOutsideEdge_endpointContact_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_insideOutsideEdge_endpointContact_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  (p ∈ H.support ∨ q ∈ H.support ∨ p ∈ (rlc_orderedContourArc c ha hb).support ∨ q ∈ (rlc_orderedContourArc c ha hb).support) ∨ (p ∈ H.support ∨ q ∈ H.support ∨ p ∈ (rlc_complementaryContourArc c ha hb).support ∨ q ∈ (rlc_complementaryContourArc c ha hb).support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_insideOutsideEdge_endpointContact_cases c hcycle ha hb H hpq hpReach hqOut

/--
[rlc_twoChannelFullPhysical_insideOutsideEdge_meets_exteriorChord_of_avoidsCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_insideOutsideEdge_meets_exteriorChord_of_avoidsCycle_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (havoid : p ∉ c.support ∧ q ∉ c.support) :
-- imply
  p ∈ H.support ∨ q ∈ H.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_insideOutsideEdge_meets_exteriorChord_of_avoidsCycle c hcycle ha hb H hpq hpReach hqOut havoid

/--
[rlc_bookPhysicalTraceNetworkBracket_contactPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_contactPlacement_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hcycle : c.IsCycle)
  (hstart : rlc_dualReflect.symm r ∈ c.support)
  (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
-- imply
  let B := rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) let k := B.support.idxOf d ∃ i j j' : Nat, i < k ∧ k < j ∧ j ≤ j' ∧ j' ≤ B.length ∧ B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧ B.getVert j' ∈ c.support ∧ B.getVert k = d ∧ (∀ l : Nat, i < l → l < j → B.getVert l ∉ c.support) ∧ (∀ l : Nat, i < l → l < j → B.getVert l ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧ rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect (B.getVert j') ∈ rlc_pathVertices gamma'.1 ∧ B.getVert i ≠ B.getVert j' ∧ (j' = j ∨ (B.getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) ∧ j < j' ∧ ∀ l : Nat, j < l → l < j' → B.getVert l ∉ c.support)) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_contactPlacement hn gamma gamma' hfaith omega hr hs hsLeft hrs c hcycle hstart hend

/--
[rlc_bookPhysicalTraceNetworkBracket_exteriorChord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_exteriorChord_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hcycle : c.IsCycle)
  (hstart : rlc_dualReflect.symm r ∈ c.support)
  (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
-- imply
  let B := rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) let k := B.support.idxOf d ∃ (i j j' : Nat) (H : (hypercubicLattice 2).Walk (B.getVert i) (B.getVert j)), H.IsPath ∧ i < k ∧ k < j ∧ j ≤ j' ∧ j' ≤ B.length ∧ B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧ B.getVert j' ∈ c.support ∧ rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect (B.getVert j') ∈ rlc_pathVertices gamma'.1 ∧ B.getVert i ≠ B.getVert j' ∧ d ∈ H.support ∧ d ∉ c.support ∧ H.support ⊆ B.support ∧ (∀ v ∈ H.support, v = B.getVert i ∨ v = B.getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧ (j' = j ∨ (B.getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) ∧ j < j' ∧ ∀ l : Nat, j < l → l < j' → B.getVert l ∉ c.support)) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_exteriorChord hn gamma gamma' hfaith omega hr hs hsLeft hrs c hcycle hstart hend

/--
[rlc_bookPhysicalTraceNetworkBracket_exteriorChord_separatorCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_exteriorChord_separatorCycles_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hcycle : c.IsCycle)
  (hstart : rlc_dualReflect.symm r ∈ c.support)
  (hend : rlc_dualReflect.symm (rlc_flipX s) ∈ c.support) :
-- imply
  let B := rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) let k := B.support.idxOf d ∃ (i j j' : Nat) (H : (hypercubicLattice 2).Walk (B.getVert i) (B.getVert j)) (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support), H.IsPath ∧ i < k ∧ k < j ∧ j ≤ j' ∧ j' ≤ B.length ∧ B.getVert j' ∈ c.support ∧ rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧ rlc_dualReflect (B.getVert j') ∈ rlc_pathVertices gamma'.1 ∧ B.getVert i ≠ B.getVert j' ∧ d ∈ H.support ∧ d ∉ c.support ∧ H.support ⊆ B.support ∧ (∀ v ∈ H.support, v = B.getVert i ∨ v = B.getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (j' = j ∨ (B.getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) ∧ j < j' ∧ ∀ l : Nat, j < l → l < j' → B.getVert l ∉ c.support)) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_exteriorChord_separatorCycles hn gamma gamma' hfaith omega hr hs hsLeft hrs c hcycle hstart hend

/--
[rlc_bookPhysicalTraceNetworkBracket_sameContact_contactExtrema](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_sameContact_contactExtrema_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hrLeft : rlc_flipX r ∈ rlc_pathVertices gamma'.1)
  (hcycle : c.IsCycle)
  (hstart : rlc_dualReflect.symm r ∈ c.support)
  (hend : rlc_dualReflect.symm (rlc_flipX r) ∈ c.support) :
-- imply
  let B := rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hr hrLeft le_rfl let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) let k := B.support.idxOf d ∃ i j : Nat, i < k ∧ k < j ∧ j ≤ B.length ∧ B.getVert i ∈ c.support ∧ B.getVert j ∈ c.support ∧ B.getVert k = d ∧ (∀ l : Nat, i < l → l < j → B.getVert l ∉ c.support) ∧ (∀ l : Nat, i < l → l < j → B.getVert l ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) ∧ rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧ (rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma'.1 ∨ B.getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_sameContact_contactExtrema hn gamma gamma' hfaith omega hr hrLeft c hcycle hstart hend

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_canonicalPhysicalTraceNetworkBracket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_canonicalPhysicalTraceNetworkBracket_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  ∃ (r s : Site 2) (hr : r ∈ rlc_pathVertices gamma.1) (hs : s ∈ rlc_pathVertices gamma.1) (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s) (Q : (hypercubicLattice 2).Walk x y), rlc_dualReflect.symm r = x ∧ rlc_dualReflect.symm (rlc_flipX s) = y ∧ Q.support = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support ∧ ∀ v ∈ Q.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_canonicalPhysicalTraceNetworkBracket hyPath h

/--
[rlc_bookPhysicalTraceNetworkBracket_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_support_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s v : Site 2}
-- given
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hv : v ∈ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support) :
-- imply
  (∃ w ∈ rlc_pathVertices gamma.1, v = rlc_dualReflect.symm w) ∨ (∃ w ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support, v = rlc_dualReflect.symm w) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, v = rlc_dualReflect.symm w := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_support_cases gamma gamma' hr hs hsLeft hrs hv

/--
[rlc_bookPhysicalTraceNetworkBracket_shiftedSource_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalTraceNetworkBracket_shiftedSource_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s a : Site 2}
-- given
  (hn : 0 < n)
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (haBox : a ∈ rect (-2 * n) (2 * n) (-n) n)
  (haBracket : phb_doubleDualShift a ∈ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support) :
-- imply
  (∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalTraceNetworkBracket_shiftedSource_cases hn gamma gamma' hr hs hsLeft hrs haBox haBracket

/--
[rlc_twoChannelFullPhysical_shiftedReach_bracket_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedReach_bracket_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s a : Site 2}
-- given
  (hn : 0 < n)
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (haBracket : phb_doubleDualShift a ∈ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support) :
-- imply
  (∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedReach_bracket_cases hn hr hs hsLeft hrs haReach haBracket

/--
[rlc_twoChannelFullPhysical_reachable_reflectedRight_axis_or_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachable_reflectedRight_axis_or_exclusive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {a w : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hwRight : w ∈ rlc_pathVertices gamma.1)
  (haw : a = rlc_flipX w) :
-- imply
  a = (gamma.1.1 : Site 2) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' a := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachable_reflectedRight_axis_or_exclusive hfaith hno haReach hwRight haw

/--
[rlc_doubleDualShift_leftRegion_iff_of_shortRoute_offLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_doubleDualShift_leftRegion_iff_of_shortRoute_offLoop_eq
  {u a : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
-- given
  (ha : a ∉ C.support)
  (hwest : (![a 0 - 1, a 1] : Site 2) ∉ C.support)
  (hshift : phb_doubleDualShift a ∉ C.support) :
-- imply
  a ∈ jec_leftRegion C ↔ phb_doubleDualShift a ∈ jec_leftRegion C := by
-- proof
  apply StatMech.Universality.rlc_doubleDualShift_leftRegion_iff_of_shortRoute_offLoop C ha hwest hshift

/--
[rlc_oppositeLoopSides_doubleDualShift_of_shortRoutes_offLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_oppositeLoopSides_doubleDualShift_of_shortRoutes_offLoop_eq
  {u p q : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
-- given
  (hopp : rlc_OppositeLoopSides C p q)
  (hp : p ∉ C.support)
  (hpWest : (![p 0 - 1, p 1] : Site 2) ∉ C.support)
  (hpShift : phb_doubleDualShift p ∉ C.support)
  (hq : q ∉ C.support)
  (hqWest : (![q 0 - 1, q 1] : Site 2) ∉ C.support)
  (hqShift : phb_doubleDualShift q ∉ C.support) :
-- imply
  rlc_OppositeLoopSides C (phb_doubleDualShift p) (phb_doubleDualShift q) := by
-- proof
  apply StatMech.Universality.rlc_oppositeLoopSides_doubleDualShift_of_shortRoutes_offLoop C hopp hp hpWest hpShift hq hqWest hqShift

/--
[rlc_doubleDualShift_oppositeSides_or_shortRoute_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_doubleDualShift_oppositeSides_or_shortRoute_contact_eq
  {u p q : Site 2}
  {C : (hypercubicLattice 2).Walk u u}
-- given
  (hopp : rlc_OppositeLoopSides C p q) :
-- imply
  rlc_OppositeLoopSides C (phb_doubleDualShift p) (phb_doubleDualShift q) ∨ ∃ z ∈ C.support, z = p ∨ z = ![p 0 - 1, p 1] ∨ z = phb_doubleDualShift p ∨ z = q ∨ z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q := by
-- proof
  apply StatMech.Universality.rlc_doubleDualShift_oppositeSides_or_shortRoute_contact C hopp

/--
[rlc_twoChannelFullPhysical_shiftedReach_shortBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedReach_shortBoundaryContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hshiftOutside : phb_doubleDualShift a ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))
  (hshiftOffCycle : phb_doubleDualShift a ∉ c.support) :
-- imply
  a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedReach_shortBoundaryContact c hcycle haReach hshiftOutside hshiftOffCycle

/--
[rlc_twoChannelFullPhysical_shiftedReach_shortRoute_boundaryEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedReach_shortRoute_boundaryEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hshiftOutside : phb_doubleDualShift a ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) :
-- imply
  ∃ p q f g : Site 2, s(p, q) ∈ (sw_lshape (a 0) (a 1) (a 0 - 1) (a 1 - 1)).edges ∧ p ∈ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ sharedPrimalEdge f g = s(p, q) ∧ s(f, g) ∈ c.edges ∧ ((rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Adj f g ∨ ¬RlcTwoChannelFullPhysicalBoundaryCarrierGeometry gamma gamma' f g) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedReach_shortRoute_boundaryEdge c hcycle haReach hshiftOutside

/--
[rlc_twoChannelFullPhysical_shiftedReach_inside_or_shortBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedReach_inside_or_shortBoundaryContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hshiftOffCycle : phb_doubleDualShift a ∉ c.support) :
-- imply
  phb_doubleDualShift a ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∨ a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedReach_inside_or_shortBoundaryContact c hcycle haReach hshiftOffCycle

/--
[rlc_twoChannelFullPhysical_sourceSplice_offContour_inside_or_tetherContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceSplice_offContour_inside_or_tetherContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u ur vr ul vl s t : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {T : (hypercubicLattice 2).Walk s t}
  {v : Site 2}
-- given
  (hcycle : c.IsCycle)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift r = v)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hvT : v ∈ T.support)
  (hvOff : v ∉ c.support) :
-- imply
  v ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∨ ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift r = v ∧ (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceSplice_offContour_inside_or_tetherContact c hcycle T hTprov hurv hulv hvT hvOff

/--
[rlc_twoChannelFullPhysical_sourceSplice_contactInterval_firstVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceSplice_contactInterval_firstVertex_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u ur vr ul vl s t : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {T : (hypercubicLattice 2).Walk s t}
  {i j : Nat}
-- given
  (hcycle : c.IsCycle)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift r = v)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hfirst : i + 1 < j)
  (hjLength : j ≤ T.length)
  (hbetween : ∀ l : Nat, i < l → l < j → T.getVert l ∉ c.support) :
-- imply
  T.getVert (i + 1) ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))) ∨ ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift r = T.getVert (i + 1) ∧ (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceSplice_contactInterval_firstVertex c hcycle T hTprov hurv hulv hfirst hjLength hbetween

/--
[rlc_twoChannelFullPhysical_sourceSplice_contactInterval_exterior_forces_tetherContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceSplice_contactInterval_exterior_forces_tetherContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u ur vr ul vl s t : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {T : (hypercubicLattice 2).Walk s t}
  {i j : Nat}
-- given
  (hcycle : c.IsCycle)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift r = v)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hfirst : i + 1 < j)
  (hjLength : j ≤ T.length)
  (hbetween : ∀ l : Nat, i < l → l < j → T.getVert l ∉ c.support)
  (hfirstOutside : T.getVert (i + 1) ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) :
-- imply
  ∃ r ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift r = T.getVert (i + 1) ∧ (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceSplice_contactInterval_exterior_forces_tetherContact c hcycle T hTprov hurv hulv hfirst hjLength hbetween hfirstOutside

/--
[rlc_walk_getVert_edge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_getVert_edge_mem_eq
  {G : SimpleGraph V}
  {a b : V}
  {W : G.Walk a b}
  {i : Nat}
-- given
  (hi : i < W.length) :
-- imply
  s(W.getVert i, W.getVert (i + 1)) ∈ W.edges := by
-- proof
  apply StatMech.Universality.rlc_walk_getVert_edge_mem W hi

/--
[rlc_twoChannelFullPhysical_sourceSplice_contactInterval_adjacentEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceSplice_contactInterval_adjacentEdge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b p p' ur vr ul vl s t : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {w : (hypercubicLattice 2).Walk p p'}
  {T : (hypercubicLattice 2).Walk s t}
  {i j : Nat}
-- given
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hTedge : ∀ e ∈ T.edges, (∀ z ∈ e, z = vr ∨ z = ur ∨ z = phb_doubleDualShift p) ∨ (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e) ∨ ∀ z ∈ e, z = vl ∨ z = ul ∨ z = phb_doubleDualShift p')
  (hij : j = i + 1)
  (hjLength : j ≤ T.length)
  (hiArc : T.getVert i ∈ (rlc_orderedContourArc c ha hb).support)
  (hjArc : T.getVert j ∈ (rlc_complementaryContourArc c ha hb).support) :
-- imply
  let e := s(T.getVert i, T.getVert j) (∀ z ∈ e, z = vr ∨ z = ur ∨ z = phb_doubleDualShift p) ∨ (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e ∧ ∀ z ∈ Sym2.map phb_doubleDualShift e₀, z ∈ c.support) ∨ ∀ z ∈ e, z = vl ∨ z = ul ∨ z = phb_doubleDualShift p' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceSplice_contactInterval_adjacentEdge c ha hb w T hTedge hij hjLength hiArc hjArc

/--
[rlc_twoChannelFullPhysical_shiftedExterior_shortBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedExterior_shortBoundaryContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (haOutside : a ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))
  (hshiftInside : phb_doubleDualShift a ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))
  (hshiftOffCycle : phb_doubleDualShift a ∉ c.support) :
-- imply
  a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedExterior_shortBoundaryContact c hcycle haOutside hshiftInside hshiftOffCycle

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_separatorSourceSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_separatorSourceSplice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y z ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hcycle : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (htrace : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk gamma gamma' (z := z) (x := x) (y := y) flipLeft)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr))
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl)) :
-- imply
  ∃ (r s : Site 2) (hr : r ∈ rlc_pathVertices gamma.1) (hs : s ∈ rlc_pathVertices gamma.1) (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s) (p q p' q' : Site 2) (T : (hypercubicLattice 2).Walk vr vl) (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (i j : Nat) (H : (hypercubicLattice 2).Walk ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j)) (hi : (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∈ c.support) (hj : (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∈ c.support), rlc_dualReflect.symm r = x ∧ rlc_dualReflect.symm (rlc_flipX s) = y ∧ sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (phb_doubleDualShift p ∈ s(ur, vr) ∨ phb_doubleDualShift q ∈ s(ur, vr)) ∧ (phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' ∈ s(ul, vl)) ∧ (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) ∧ (∃ v ∈ T.support, v 0 = -1 ∧ (v = vr ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, a 0 = 0 ∧ phb_doubleDualShift a = v)) ∧ (∃ (v : Site 2) (k : Nat), k ≤ T.length ∧ T.getVert k = v ∧ v 0 = -1 ∧ (v ∈ c.support ∨ ∃ i' j' : Nat, i' < k ∧ k < j' ∧ j' ≤ T.length ∧ T.getVert i' ∈ c.support ∧ T.getVert j' ∈ c.support ∧ ∀ l : Nat, i' < l → l < j' → T.getVert l ∉ c.support)) ∧ ((∃ v ∈ T.support, v ∈ (rlc_orderedContourArc c hx hy).support ∧ v ∈ (rlc_complementaryContourArc c hx hy).support) ∨ ∃ i' j' : Nat, i' < j' ∧ j' ≤ T.length ∧ T.getVert i' ∈ (rlc_orderedContourArc c hx hy).support ∧ T.getVert j' ∈ (rlc_complementaryContourArc c hx hy).support ∧ ∀ l : Nat, i' < l → l < j' → T.getVert l ∉ c.support) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) 0 = -1 ∧ ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) 1 < -1 ∨ ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) 0 < -1) ∧ rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ∈ rlc_pathVertices gamma.1 ∧ (rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) ∈ rlc_pathVertices gamma'.1 ∨ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) ∧ ((((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) 0 = -1 ∧ 0 ≤ ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) 1 ∨ 0 ≤ ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) 0) ∨ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) ∧ (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ∈ H.support ∧ (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ∉ c.support ∧ (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ∉ V.support ∧ H.support ⊆ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support ∧ (∀ v ∈ H.support, v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧ (∀ v ∈ V.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1)) ∧ qr.support ⊆ V.support ∧ ql.support ⊆ V.support ∧ T.support ⊆ V.support ∧ (∀ v ∈ H.support, v ∈ V.support → v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v ∧ (a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧ ((∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w)) ∧ (∀ v ∈ V.support, v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil (rlc_dualReflect x) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 (rlc_dualReflect x)).2 hxPath)).map rlc_dualReflectSymmLatticeHom).support ∨ v ∈ qr.support ∨ v = ur ∨ v = vr ∨ v ∈ T.support ∨ v = vl ∨ v = ul ∨ v ∈ ql.support ∨ v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil (rlc_dualReflect y) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_dualReflect y)).2 hyPath)).map rlc_dualReflectSymmLatticeHom).support) ∧ ∀ e ∈ V.edges, e ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil (rlc_dualReflect x) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 (rlc_dualReflect x)).2 hxPath)).map rlc_dualReflectSymmLatticeHom).edges ∨ e ∈ qr.edges ∨ e = s(ur, vr) ∨ e ∈ T.edges ∨ e = s(ul, vl) ∨ e ∈ ql.edges ∨ e ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil (rlc_dualReflect y) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_dualReflect y)).2 hyPath)).map rlc_dualReflectSymmLatticeHom).edges := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_separatorSourceSplice hn hfaith c hcycle hx hy hxPath hyPath htrace qr rr ql hrow rl hurv hulv hdecR hdecL

/--
[rlc_twoChannelFullPhysical_rowTwo_HVContact_axisFree_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowTwo_HVContact_axisFree_classification_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s : Site 2}
  {u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {i j : Nat}
  {H : (hypercubicLattice 2).Walk ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j)}
  {aV bV : Site 2}
  {V : (hypercubicLattice 2).Walk aV bV}
  {v : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hrAxis : r ≠ (gamma.1.1 : Site 2))
  (hHB : H.support ⊆ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support)
  (hHV : ∀ v ∈ H.support, v ∈ V.support → v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v ∧ (a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧ ((∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w))
  (hvH : v ∈ H.support)
  (hvV : v ∈ V.support) :
-- imply
  v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v ∧ (a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧ (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' a ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowTwo_HVContact_axisFree_classification hfaith hno hr hs hsLeft hrs hrAxis hHB hHV hvH hvV

/--
[rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_ne_chordEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_ne_chordEndpoints_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {r s : Site 2}
  {hr : r ∈ rlc_pathVertices gamma.1}
  {hs : s ∈ rlc_pathVertices gamma.1}
  {hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1}
  {hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hiRight : rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ∈ rlc_pathVertices gamma.1)
  (hjProvenance : rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) ∈ rlc_pathVertices gamma'.1 ∨ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
-- imply
  ur ≠ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∧ ur ≠ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_ne_chordEndpoints hn hrow hiRight hjProvenance

/--
[rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_sourceWitness_of_HV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_sourceWitness_of_HV_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {r s : Site 2}
  {hr : r ∈ rlc_pathVertices gamma.1}
  {hs : s ∈ rlc_pathVertices gamma.1}
  {hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1}
  {hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hiRight : rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ∈ rlc_pathVertices gamma.1)
  (hjProvenance : rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) ∈ rlc_pathVertices gamma'.1 ∨ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2))
  (hclass : ur = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ ur = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = ur ∧ (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' a ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w)) :
-- imply
  ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = ur ∧ (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' a ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_sourceWitness_of_HV hn hrow hiRight hjProvenance hclass

/--
[rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_HV_sourceWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_HV_sourceWitness_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {r s : Site 2}
  {u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {i j : Nat}
  {H : (hypercubicLattice 2).Walk ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j)}
  {aV bV : Site 2}
  {V : (hypercubicLattice 2).Walk aV bV}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hs : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s)
  (hrAxis : r ≠ (gamma.1.1 : Site 2))
  (hHB : H.support ⊆ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support)
  (hHV : ∀ v ∈ H.support, v ∈ V.support → v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v ∧ (a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧ ((∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w))
  (hiRight : rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ∈ rlc_pathVertices gamma.1)
  (hjProvenance : rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) ∈ rlc_pathVertices gamma'.1 ∨ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2))
  (hurH : ur ∈ H.support)
  (hurV : ur ∈ V.support) :
-- imply
  ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = ur ∧ (a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧ (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' a ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowTwo_reflectedLeftTerminal_HV_sourceWitness hn hfaith hno hrow hr hs hsLeft hrs hrAxis hHB hHV hiRight hjProvenance hurH hurV

/--
[rlc_twoChannelFullPhysical_Hclean_cycleContact_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_Hclean_cycleContact_endpoints_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s : Site 2}
  {hr : r ∈ rlc_pathVertices gamma.1}
  {hs : s ∈ rlc_pathVertices gamma.1}
  {hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1}
  {hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s}
  {u v : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {i j : Nat}
  {H : (hypercubicLattice 2).Walk ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j)}
-- given
  (hclean : ∀ z ∈ H.support, z = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ z = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ (z ∉ c.support ∧ z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hvH : v ∈ H.support)
  (hvC : v ∈ c.support) :
-- imply
  v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_Hclean_cycleContact_endpoints hclean hvH hvC

/--
[rlc_twoChannelFullPhysical_Hclean_shiftedReflectedRight_eq_firstEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_Hclean_shiftedReflectedRight_eq_firstEndpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {r s p v : Site 2}
  {hr : r ∈ rlc_pathVertices gamma.1}
  {hs : s ∈ rlc_pathVertices gamma.1}
  {hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1}
  {hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s}
  {u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {i j : Nat}
  {H : (hypercubicLattice 2).Walk ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j)}
  {w : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hclean : ∀ z ∈ H.support, z = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ z = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ (z ∉ c.support ∧ z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hvH : v ∈ H.support)
  (hvC : v ∈ c.support)
  (hshift : phb_doubleDualShift p = v)
  (hwRight : w ∈ rlc_pathVertices gamma.1)
  (hpw : p = rlc_flipX w)
  (hjProvenance : rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) ∈ rlc_pathVertices gamma'.1 ∨ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
-- imply
  v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_Hclean_shiftedReflectedRight_eq_firstEndpoint hfaith hclean hvH hvC hshift hwRight hpw hjProvenance

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceEdge_separatorContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceEdge_separatorContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u x y z ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hcycle : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (htrace : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk gamma gamma' (z := z) (x := x) (y := y) flipLeft)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowTwo gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr))
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl)) :
-- imply
  ∃ (r s : Site 2) (hr : r ∈ rlc_pathVertices gamma.1) (hs : s ∈ rlc_pathVertices gamma.1) (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1) (hrs : (rlc_ambientCrossingWalk gamma.1).support.idxOf r ≤ (rlc_ambientCrossingWalk gamma.1).support.idxOf s) (p q p' q' : Site 2) (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (i j : Nat) (H : (hypercubicLattice 2).Walk ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j)) (hi : (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∈ c.support) (hj : (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∈ c.support), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i) ∈ rlc_pathVertices gamma.1 ∧ (rlc_dualReflect ((rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) ∈ rlc_pathVertices gamma'.1 ∨ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) ∧ H.support ⊆ (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).support ∧ (∀ v ∈ H.support, v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧ (∀ v ∈ H.support, v ∈ V.support → v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ v = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v ∧ (a ∈ c.support ∨ (![a 0 - 1, a 1] : Site 2) ∈ c.support) ∧ ((∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w)) ∧ (p = vr → p ∈ V.support ∧ p ∈ c.support) ∧ (∀ v ∈ V.support, v ∈ (((rlc_ambientCrossingWalk gamma.1).takeUntil (rlc_dualReflect x) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 (rlc_dualReflect x)).2 hxPath)).map rlc_dualReflectSymmLatticeHom).support ∨ v ∈ qr.support ∨ v = ur ∨ v = vr ∨ (∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) ∨ v = vl ∨ v = ul ∨ v ∈ ql.support ∨ v ∈ (((rlc_ambientCrossingWalk gamma'.1).dropUntil (rlc_dualReflect y) ((rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 (rlc_dualReflect y)).2 hyPath)).map rlc_dualReflectSymmLatticeHom).support) ∧ (p ∈ H.support → p = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert i ∨ p = (rlc_bookPhysicalTraceNetworkBracket gamma gamma' hr hs hsLeft hrs).getVert j) ∧ (q = ur → q ∉ H.support) ∧ (p ∈ c.support ∨ q ∈ c.support ∨ (q ∈ H.support ∧ ((p = ur ∧ phb_doubleDualShift q = vr ∧ ∃ w ∈ rlc_pathVertices gamma'.1, q = ![w 0 - 1, w 1] ∨ q = ![w 0, w 1 - 1]) ∨ (p = vr ∧ phb_doubleDualShift q = ur ∧ ∃ w ∈ rlc_pathVertices gamma'.1, q = w ∧ ((sharedPrimalEdge ur vr = s((![w 0, w 1 - 1] : Site 2), w) ∧ s((![w 0, w 1 - 1] : Site 2), w) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) ∨ (sharedPrimalEdge ur vr = s((![w 0 - 1, w 1] : Site 2), w) ∧ s((![w 0 - 1, w 1] : Site 2), w) ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)))))) ∧ ((p ∈ H.support ∨ q ∈ H.support ∨ p ∈ (rlc_orderedContourArc c hi hj).support ∨ q ∈ (rlc_orderedContourArc c hi hj).support) ∨ (p ∈ H.support ∨ q ∈ H.support ∨ p ∈ (rlc_complementaryContourArc c hi hj).support ∨ q ∈ (rlc_complementaryContourArc c hi hj).support)) ∧ ((phb_doubleDualShift p = vr ∧ q = ur) ∨ (p = ur ∧ phb_doubleDualShift q = vr) ∨ (p = vr ∧ phb_doubleDualShift q = ur)) ∧ (RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∨ (p 0 = -2 * n ∨ p 0 = 2 * n ∨ p 1 = -n ∨ p 1 = n)) ∧ (p = vr → RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∨ p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧ sharedPrimalEdge ur vr ∉ rlc_connectorFourTraceEdges gamma gamma')) ∧ (p = vr → RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' ur vr ∨ (p ∈ c.support ∧ ((p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∨ ∃ z : Site 2, RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ sharedPrimalEdge ur vr ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' omega s(p, z) = true ∧ (s(p, z) ∈ rlc_connectorFourTraceEdges gamma gamma' ∨ (z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1))))) ∧ (phb_doubleDualShift p = vr ∨ p = ur ∨ p = vr) ∧ (phb_doubleDualShift p ∈ c.support ∨ p ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_sourceEdge_separatorContact hn hfaith hno c hcycle hx hy hxPath hyPath htrace qr rr ql hrow rl hurv hulv hdecR hdecL

/--
[rlc_bookOuterTraceNetworkArc_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookOuterTraceNetworkArc_mem_rect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {s v : Site 2}
-- given
  (hsRight : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hv : v ∈ (rlc_bookOuterTraceNetworkArc gamma gamma' hsRight hsLeft).support) :
-- imply
  v ∈ rect (-2 * n - 2) (2 * n + 2) (-n) (n + 2) := by
-- proof
  apply StatMech.Universality.rlc_bookOuterTraceNetworkArc_mem_rect gamma gamma' hsRight hsLeft hv

/--
[rlc_bookPhysicalOuterTraceNetworkArc_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookPhysicalOuterTraceNetworkArc_mem_rect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {s v : Site 2}
-- given
  (hsRight : s ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hv : v ∈ (rlc_bookPhysicalOuterTraceNetworkArc gamma gamma' hsRight hsLeft).support) :
-- imply
  v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_bookPhysicalOuterTraceNetworkArc_mem_rect gamma gamma' hsRight hsLeft hv

/--
[rlc_twoChannelFullPhysical_wallFamilyRowTwo_physicalOuterTraceNetworkBracketWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowTwo_physicalOuterTraceNetworkBracketWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z x y : Site 2}
  {flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2)}
-- given
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (h : RlcTwoChannelFullPhysicalWallFamilyRowTwoTraceBracketWalk gamma gamma' (z := z) (x := x) (y := y) flipLeft) :
-- imply
  ∃ (r s : Site 2) (Q : (hypercubicLattice 2).Walk x y), r ∈ rlc_bookFlippedTraceIntersectionSet gamma gamma' ∧ ∃ (hsRight : s ∈ rlc_pathVertices gamma.1) (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1), rlc_dualReflect.symm z ∈ Q.support ∧ (rlc_bookPhysicalOuterTraceNetworkArc gamma gamma' hsRight hsLeft).support ⊆ Q.support ∧ ∀ v ∈ Q.support, v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowTwo_physicalOuterTraceNetworkBracketWalk hyPath h

/--
[rlc_bookRowOne_flippedLeftEndpoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOne_flippedLeftEndpoint_mem_eq
  {n : Int}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  rlc_flipX (rlc_flipX (gamma'.1.2.1 : Site 2)) ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_bookRowOne_flippedLeftEndpoint_mem gamma'

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_exteriorPoint_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_exteriorPoint_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1) :
-- imply
  rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_exteriorPoint_mem gamma gamma' hzRight

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_isPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_isPath_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1) :
-- imply
  (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).IsPath := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_isPath hn hfaith hzRight

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_right_index_le_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_right_index_le_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
  {j : Nat}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hjRight : rlc_dualReflect ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j) ∈ rlc_pathVertices gamma.1) :
-- imply
  j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support.idxOf (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_right_index_le_exterior hn hfaith hzRight hjLength hjRight

/--
[rlc_bookSimpleTraceNetworkBracket_left_index_ge_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookSimpleTraceNetworkBracket_left_index_ge_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s w : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hw : w ∈ (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support)
  (hwLeft : w ∈ rlc_pathVertices gamma'.1) :
-- imply
  (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support.idxOf (![(2 * n + 2), n + 2] : Site 2) ≤ (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support.idxOf w := by
-- proof
  apply StatMech.Universality.rlc_bookSimpleTraceNetworkBracket_left_index_ge_exterior hn hfaith hr hsLeft hw hwLeft

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_left_index_ge_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_left_index_ge_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
  {j : Nat}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hjLeft : rlc_dualReflect ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j) ∈ rlc_pathVertices gamma'.1) :
-- imply
  (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support.idxOf (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ≤ j := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_left_index_ge_exterior hn hfaith hzRight hjLength hjLeft

/--
[rlc_bookExteriorEndpointDetour_takeUntil_topRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookExteriorEndpointDetour_takeUntil_topRight_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n} :
-- imply
  let D := rlc_bookExteriorEndpointDetour gamma gamma' let d : Site 2 := ![2 * n + 2, n + 2] let hd : d ∈ D.support := rlc_bookExteriorEndpointDetour_topRight_mem gamma gamma' ∀ v ∈ (D.takeUntil d hd).support, 2 * n ≤ v 0 := by
-- proof
  apply StatMech.Universality.rlc_bookExteriorEndpointDetour_takeUntil_topRight gamma gamma'

/--
[rlc_bookSimpleTraceNetworkBracket_collar_index_ge_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookSimpleTraceNetworkBracket_collar_index_ge_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {r s : Site 2}
-- given
  (hn : 0 < n)
  (hr : r ∈ rlc_pathVertices gamma.1)
  (hsLeft : rlc_flipX s ∈ rlc_pathVertices gamma'.1)
  (hcollar : (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) ∈ (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support) :
-- imply
  (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support.idxOf (![(2 * n + 2), n + 2] : Site 2) ≤ (rlc_bookSimpleTraceNetworkBracket gamma gamma' hr hsLeft).support.idxOf (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookSimpleTraceNetworkBracket_collar_index_ge_exterior hn hr hsLeft hcollar

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_collar_index_ge_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_collar_index_ge_exterior_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
  {j : Nat}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hjCollar : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
-- imply
  (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support.idxOf (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) ≤ j := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_collar_index_ge_exterior hn hfaith hzRight hjLength hjCollar

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_mem_rect_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z v : Site 2}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hv : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support) :
-- imply
  v ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 1) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_mem_rect gamma gamma' hzRight hv

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z v : Site 2}
-- given
  (hn : 0 < n)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hvBracket : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support)
  (hvBoundary : v ∈ (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support) :
-- imply
  rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨ v = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_boundaryContact_provenance hn gamma gamma' omega hzRight hvBracket hvBoundary

/--
[rlc_cycleVertex_mem_graphSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_cycleVertex_mem_graphSupport_eq
  {G : SimpleGraph V}
  {u v : V}
  {c : G.Walk u u}
-- given
  (hcycle : c.IsCycle)
  (hv : v ∈ c.support) :
-- imply
  v ∈ G.support := by
-- proof
  apply StatMech.Universality.rlc_cycleVertex_mem_graphSupport c hcycle hv

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_beforeExterior_boundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_beforeExterior_boundaryContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hcycle : c.IsCycle)
  (hiLength : i ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hik : i < (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support.idxOf (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)))
  (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∈ c.support) :
-- imply
  rlc_dualReflect ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i) ∈ rlc_pathVertices gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_beforeExterior_boundaryContact hn hfaith hzRight c hcycle hiLength hik hi

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_afterExterior_boundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_afterExterior_boundaryContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {j : Nat}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hcycle : c.IsCycle)
  (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hkj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support.idxOf (rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2)) < j)
  (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∈ c.support) :
-- imply
  rlc_dualReflect ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j) ∈ rlc_pathVertices gamma'.1 ∨ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_afterExterior_boundaryContact hn hfaith hzRight c hcycle hjLength hkj hj

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_cycleEndpoint_provenance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_cycleEndpoint_provenance_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z u v : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hcycle : c.IsCycle)
  (hvBracket : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support)
  (hvCycle : v ∈ c.support) :
-- imply
  rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨ v = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2) := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_cycleEndpoint_provenance hn gamma gamma' omega hzRight c hcycle hvBracket hvCycle

/--
[rlc_twoChannelFullPhysical_cleanChord_insideOutside_endpoint_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_cleanChord_insideOutside_endpoint_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  p = a ∨ p = b ∨ q ∈ H.support ∨ p ∈ c.support ∨ q ∈ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_cleanChord_insideOutside_endpoint_cases c hcycle ha hb H hclean hpqAdj hpReach hqOut

/--
[rlc_exteriorWalk_contactInterval_separatorCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorWalk_contactInterval_separatorCycles_eq
  {G : SimpleGraph (Site 2)}
  {u a b d : Site 2}
  {c : G.Walk u u}
  {B : (hypercubicLattice 2).Walk a b}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (hcycle : c.IsCycle)
  (hBPath : B.IsPath)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hdB : d ∈ B.support)
  (hdC : d ∉ c.support)
  (hdOutside : d ∉ jec_leftRegion (c.mapLe hG)) :
-- imply
  ∃ (i j : Nat) (H : (hypercubicLattice 2).Walk (B.getVert i) (B.getVert j)) (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support), H.IsPath ∧ d ∈ H.support ∧ d ∉ c.support ∧ H.support ⊆ B.support ∧ (∀ v ∈ H.support, v = B.getVert i ∨ v = B.getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe hG))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe hG).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe hG).reverse).IsCycle := by
-- proof
  apply StatMech.Universality.rlc_exteriorWalk_contactInterval_separatorCycles hG c hcycle B hBPath ha hb hdB hdC hdOutside

/--
[rlc_walk_mem_indexInterval_or_before_or_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_walk_mem_indexInterval_or_before_or_after_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
  {B : G.Walk a b}
  {i j : Nat}
  {z : V}
-- given
  (hiLength : i ≤ B.length)
  (hij : i ≤ j)
  (hjLength : j ≤ B.length)
  (hz : z ∈ B.support) :
-- imply
  z ∈ (rlc_walkIndexInterval B i j hiLength hij hjLength).support ∨ (∃ k : Nat, k < i ∧ B.getVert k = z) ∨ ∃ k : Nat, j < k ∧ k ≤ B.length ∧ B.getVert k = z := by
-- proof
  apply StatMech.Universality.rlc_walk_mem_indexInterval_or_before_or_after B i j hiLength hij hjLength hz

/--
[rlc_exteriorBracket_contact_localized_to_indexInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorBracket_contact_localized_to_indexInterval_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b : V}
  {B : G.Walk a b}
  {i j : Nat}
  {A : List V}
-- given
  (hiLength : i ≤ B.length)
  (hij : i ≤ j)
  (hjLength : j ≤ B.length)
  (P : V → Prop)
  (hcontact : (∃ z ∈ B.support, P z) ∨ ∃ z ∈ A, P z) :
-- imply
  (∃ z ∈ (rlc_walkIndexInterval B i j hiLength hij hjLength).support, P z) ∨ (∃ k : Nat, k < i ∧ P (B.getVert k)) ∨ (∃ k : Nat, j < k ∧ k ≤ B.length ∧ P (B.getVert k)) ∨ ∃ z ∈ A, P z := by
-- proof
  apply StatMech.Universality.rlc_exteriorBracket_contact_localized_to_indexInterval B i j hiLength hij hjLength P A hcontact

/--
[rlc_exteriorWalk_contactInterval_separatorCycles_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorWalk_contactInterval_separatorCycles_indexed_eq
  {G : SimpleGraph (Site 2)}
  {u a b d : Site 2}
  {c : G.Walk u u}
  {B : (hypercubicLattice 2).Walk a b}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (hcycle : c.IsCycle)
  (hBPath : B.IsPath)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hdB : d ∈ B.support)
  (hdC : d ∉ c.support)
  (hdOutside : d ∉ jec_leftRegion (c.mapLe hG)) :
-- imply
  ∃ (i j : Nat) (hiLength : i ≤ B.length) (hij : i ≤ j) (hjLength : j ≤ B.length) (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support), let H := rlc_walkIndexInterval B i j hiLength hij hjLength i < B.support.idxOf d ∧ B.support.idxOf d < j ∧ H.IsPath ∧ d ∈ H.support ∧ d ∉ c.support ∧ H.support ⊆ B.support ∧ (∀ v ∈ H.support, v = B.getVert i ∨ v = B.getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe hG))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe hG).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe hG).reverse).IsCycle := by
-- proof
  apply StatMech.Universality.rlc_exteriorWalk_contactInterval_separatorCycles_indexed hG c hcycle B hBPath ha hb hdB hdC hdOutside

/--
[rlc_exteriorWalk_exteriorContact_reselect_separatorCycles_indexed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_exteriorWalk_exteriorContact_reselect_separatorCycles_indexed_eq
  {G : SimpleGraph (Site 2)}
  {u a b s t z : Site 2}
  {c : G.Walk u u}
  {B : (hypercubicLattice 2).Walk a b}
  {W : (hypercubicLattice 2).Walk s t}
-- given
  (hG : G ≤ hypercubicLattice 2)
  (hcycle : c.IsCycle)
  (hBPath : B.IsPath)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hzW : z ∈ W.support)
  (hzB : z ∈ B.support)
  (hzC : z ∉ c.support)
  (hzOutside : z ∉ jec_leftRegion (c.mapLe hG)) :
-- imply
  ∃ (i j : Nat) (hiLength : i ≤ B.length) (hij : i ≤ j) (hjLength : j ≤ B.length) (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support), let H := rlc_walkIndexInterval B i j hiLength hij hjLength H.IsPath ∧ z ∈ W.support ∧ z ∈ H.support ∧ H.support ⊆ B.support ∧ (∀ v ∈ H.support, v = B.getVert i ∨ v = B.getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe hG))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe hG).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe hG).reverse).IsCycle := by
-- proof
  apply StatMech.Universality.rlc_exteriorWalk_exteriorContact_reselect_separatorCycles_indexed hG c hcycle B hBPath ha hb W hzW hzB hzC hzOutside

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hcycle : c.IsCycle)
  (hstart : rlc_dualReflect.symm z ∈ c.support)
  (hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈ c.support) :
-- imply
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∃ (i j : Nat) (H : (hypercubicLattice 2).Walk (B.getVert i) (B.getVert j)) (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support), H.IsPath ∧ d ∈ H.support ∧ d ∉ c.support ∧ H.support ⊆ B.support ∧ (∀ v ∈ H.support, v = B.getVert i ∨ v = B.getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles hn hfaith hzRight c hcycle hstart hend

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles_indexed_oriented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles_indexed_oriented_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z u : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hcycle : c.IsCycle)
  (hstart : rlc_dualReflect.symm z ∈ c.support)
  (hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈ c.support) :
-- imply
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight let d := rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∃ (i j : Nat) (hiLength : i ≤ B.length) (hij : i ≤ j) (hjLength : j ≤ B.length) (hi : B.getVert i ∈ c.support) (hj : B.getVert j ∈ c.support), let H := rlc_walkIndexInterval B i j hiLength hij hjLength i < B.support.idxOf d ∧ B.support.idxOf d < j ∧ H.IsPath ∧ d ∈ H.support ∧ d ∉ c.support ∧ H.support ⊆ B.support ∧ (∀ v ∈ H.support, v = B.getVert i ∨ v = B.getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ rlc_dualReflect (B.getVert i) ∈ rlc_pathVertices gamma.1 ∧ (rlc_dualReflect (B.getVert j) ∈ rlc_pathVertices gamma'.1 ∨ B.getVert j = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_separatorCycles_indexed_oriented hn hfaith hzRight c hcycle hstart hend

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_separatorSourceSplice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_separatorSourceSplice_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hcycle : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ (T : (hypercubicLattice 2).Walk vr vl) (i j : Nat) (H : (hypercubicLattice 2).Walk ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i) ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j)) (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∈ c.support) (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∈ c.support), (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) ∧ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧ H.IsPath ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈ H.support ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∉ c.support ∧ H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support ∧ (∀ v ∈ H.support, v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∨ v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_separatorSourceSplice hn hfaith hnoGood c hcycle hx hy hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_reflectedLeftTerminalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_reflectedLeftTerminalInterval_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur ul : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul)) :
-- imply
  ∃ R : (hypercubicLattice 2).Walk ur ul, ∀ v ∈ R.support, ∃ w ∈ rlc_pathVertices gamma'.1, phb_doubleDualShift w = v := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_reflectedLeftTerminalInterval hrow horder

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul)) :
-- imply
  ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p'), Q.support ⊆ W.support ∧ (∀ z ∈ Q.support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) ∧ ∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hc : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ z ∈ H.support, z = a ∨ z = b ∨ (z ∉ c.support ∧ z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c ha hb).edges)
  (hcycles : (H.append ((rlc_orderedContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle)
  (havoid : (∀ z, (z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) → z ∉ (rlc_orderedContourArc c ha hb).support) ∨ (∀ z, (z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) → z ∉ (rlc_complementaryContourArc c ha hb).support)) :
-- imply
  ∃ z ∈ H.support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord c hc ha hb H hclean hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder hterminalNe hRArc hLArc hcycles havoid

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_meets_cleanChord_or_bothArcs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_meets_cleanChord_or_bothArcs_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hc : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ z ∈ H.support, z = a ∨ z = b ∨ (z ∉ c.support ∧ z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c ha hb).edges)
  (hcycles : (H.append ((rlc_orderedContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle) :
-- imply
  ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p'), Q.support ⊆ W.support ∧ (∀ z ∈ Q.support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) ∧ (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧ ((∃ z ∈ W.support, z ∈ H.support) ∨ ((∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c ha hb).support) ∧ ∃ z ∈ W.support, z ∈ (rlc_complementaryContourArc c ha hb).support)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_meets_cleanChord_or_bothArcs c hc ha hb H hclean hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder hterminalNe hRArc hLArc hcycles

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_shiftWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_shiftWalk_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul)) :
-- imply
  ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p') (T : (hypercubicLattice 2).Walk vr vl), Q.support ⊆ W.support ∧ (∀ z ∈ Q.support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) ∧ (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧ (∀ z ∈ W.support, phb_doubleDualShift z ∈ T.support) ∧ (∀ e ∈ W.edges, Sym2.map phb_doubleDualShift e ∈ T.edges) ∧ (∀ e ∈ T.edges, ∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = e) ∧ ∀ z ∈ T.support, z ∈ rect (-2 * n - 3) (2 * n + 1) (-n - 3) (n + 1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_shiftWalk hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpReach hpReach' hpShift hpShift' horder

/--
[rlc_twoChannelFullPhysical_terminalPrimalFlank_meets_cleanChord_or_bothArcs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_terminalPrimalFlank_meets_cleanChord_or_bothArcs_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {Q : (hypercubicLattice 2).Walk q q'}
  {W : (hypercubicLattice 2).Walk p p'}
-- given
  (hc : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ z ∈ H.support, z = a ∨ z = b ∨ (z ∉ c.support ∧ z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hQW : Q.support ⊆ W.support)
  (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c ha hb).edges)
  (hcycles : (H.append ((rlc_orderedContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle) :
-- imply
  (∃ z ∈ W.support, z ∈ H.support) ∨ ((∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c ha hb).support) ∧ ∃ z ∈ W.support, z ∈ (rlc_complementaryContourArc c ha hb).support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_terminalPrimalFlank_meets_cleanChord_or_bothArcs c hc ha hb H hclean hurv hulv hpq hpq' hpqAdj hpqAdj' Q W hQW hterminalNe hRArc hLArc hcycles

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_BChanging](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_BChanging_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul)) :
-- imply
  ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p') (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2), Q.support ⊆ W.support ∧ (∀ z ∈ Q.support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) ∧ (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ ((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ul vl)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_BChanging hn hfaith A B hAright hAleft hBright hBleft hnoPair hxPath hyPath qr ql hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpReach hpReach' hpShift hpShift' horder

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_twoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_twoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hc : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ z ∈ H.support, z = a ∨ z = b ∨ (z ∉ c.support ∧ z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c ha hb).edges)
  (hcycles : (H.append ((rlc_orderedContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle) :
-- imply
  ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p') (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2), Q.support ⊆ W.support ∧ (∀ z ∈ Q.support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) ∧ (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ (((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ul vl)) ∧ ((∃ z ∈ W.support, z ∈ H.support) ∨ ((∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c ha hb).support) ∧ ∃ z ∈ W.support, z ∈ (rlc_complementaryContourArc c ha hb).support))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_twoChannel hn hfaith A B hAright hAleft hBright hBleft hnoPair c hc ha hb H hclean hxPath hyPath qr ql hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpReach hpReach' hpShift hpShift' horder hterminalNe hRArc hLArc hcycles

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord_or_bothArcs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord_or_bothArcs_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hc : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ z ∈ H.support, z = a ∨ z = b ∨ (z ∉ c.support ∧ z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c ha hb).edges)
  (hcycles : (H.append ((rlc_orderedContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))).reverse).IsCycle) :
-- imply
  (∃ z ∈ H.support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) ∨ ((∃ z ∈ (rlc_orderedContourArc c ha hb).support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) ∧ ∃ z ∈ (rlc_complementaryContourArc c ha hb).support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_cleanChord_or_bothArcs c hc ha hb H hclean hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder hterminalNe hRArc hLArc hcycles

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice_crosscut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice_crosscut_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {rr : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vr y}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {rl : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk vl x}
-- given
  (hnoGood : ¬RlcTwoChannelFullPhysicalGoodComponentContacts gamma gamma' omega)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hdecR : rlc_orderedContourArc c hx hy = (qr.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hurv rr))
  (hdecL : (rlc_complementaryContourArc c hx hy).reverse = (ql.mapLe (rlc_twoChannelFullPhysicalGoodBoundaryGraph_le gamma gamma' omega)).append (.cons hulv rl)) :
-- imply
  ∃ T : (hypercubicLattice 2).Walk vr vl, (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' omega, phb_doubleDualShift a = v) ∧ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧ ((∃ v ∈ T.support, v ∈ (rlc_orderedContourArc c hx hy).support ∧ v ∈ (rlc_complementaryContourArc c hx hy).support) ∨ ∃ (i j : Nat) (hi : i ≤ T.length) (hij : i ≤ j) (hj : j ≤ T.length), i < j ∧ T.getVert i ∈ (rlc_orderedContourArc c hx hy).support ∧ T.getVert j ∈ (rlc_complementaryContourArc c hx hy).support ∧ ∀ v ∈ (rlc_walkIndexInterval T i j hi hij hj).support, v = T.getVert i ∨ v = T.getVert j ∨ v ∉ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_orderedSourceSplice_crosscut hnoGood c hx hy hzRight hzLeft hxPath hyPath qr rr ql hrow rl hurv hulv hxz hyAxis hdecR hdecL

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminalReducedSourceResidue_separatorContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminalReducedSourceResidue_separatorContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hres : RlcTwoChannelFullPhysicalReflectedLeftTerminalReducedSourceResidue gamma gamma' omega f g) :
-- imply
  (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧ ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue gamma gamma' omega p q) ∨ p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧ ((p ∈ H.support ∨ q ∈ H.support ∨ p ∈ (rlc_orderedContourArc c ha hb).support ∨ q ∈ (rlc_orderedContourArc c ha hb).support) ∨ (p ∈ H.support ∨ q ∈ H.support ∨ p ∈ (rlc_complementaryContourArc c ha hb).support ∨ q ∈ (rlc_complementaryContourArc c ha hb).support)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminalReducedSourceResidue_separatorContact c hcycle ha hb H hres

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminalReducedSourceResidue_cleanSeparatorContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminalReducedSourceResidue_cleanSeparatorContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hres : RlcTwoChannelFullPhysicalReflectedLeftTerminalReducedSourceResidue gamma gamma' omega f g) :
-- imply
  (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧ ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue gamma gamma' omega p q) ∨ p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧ (p = a ∨ p = b ∨ q ∈ H.support ∨ p ∈ c.support ∨ q ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminalReducedSourceResidue_cleanSeparatorContact c hcycle ha hb H hclean hres

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hres : RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B f g) :
-- imply
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_reflectedPathEdges gamma'.1) ∨ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧ (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧ ∃ p q : Site 2, sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) p q) ∨ p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧ (p = a ∨ p = b ∨ q ∈ H.support ∨ p ∈ c.support ∨ q ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminalExactResidue_cleanSeparatorContact A B c hcycle ha hb H hclean hres

/--
[rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b ur vr ul vl p p' f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {W : (hypercubicLattice 2).Walk p p'}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hchanging : ((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ul vl))) :
-- imply
  ((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ul vl)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks A B c hcycle ha hb H hclean W hchanging

/--
[rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_exteriorBracketContact_reselect_cleanTwoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_exteriorBracketContact_reselect_cleanTwoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u z ur vr ul vl p p' f g v : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {W : (hypercubicLattice 2).Walk p p'}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hcycle : c.IsCycle)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hstart : rlc_dualReflect.symm z ∈ c.support)
  (hend : rlc_dualReflect.symm (gamma'.1.2.1 : Site 2) ∈ c.support)
  (hvW : v ∈ W.support)
  (hvB : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support)
  (hvC : v ∉ c.support)
  (hvOutside : v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))))
  (hchanging : ((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ul vl))) :
-- imply
  ∃ (i j : Nat) (H : (hypercubicLattice 2).Walk ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i) ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j)) (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∈ c.support) (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∈ c.support), H.IsPath ∧ v ∈ W.support ∧ v ∈ H.support ∧ H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support ∧ (∀ w ∈ H.support, w = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∨ w = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∨ (w ∉ c.support ∧ w ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ ((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ul vl)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_exteriorBracketContact_reselect_cleanTwoChannel hn hfaith A B c hcycle hzRight hstart hend W hvW hvB hvC hvOutside hchanging

/--
[rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks_fullBracket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks_fullBracket_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b z x y ur vr ul vl p q p' q' f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
  {Q : (hypercubicLattice 2).Walk q q'}
  {W : (hypercubicLattice 2).Walk p p'}
-- given
  (hn : 0 < n)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c hx hy).edges)
  (hQW : Q.support ⊆ W.support)
  (hchanging : ((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ul vl))) :
-- imply
  (((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ul vl)) ∧ ((∃ v ∈ W.support, v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support) ∨ ((∃ v ∈ W.support, v ∈ (rlc_orderedContourArc c hx hy).support) ∧ ∃ v ∈ W.support, v ∈ (rlc_complementaryContourArc c hx hy).support))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_selectedPrimalFlank_BChanging_cleanTerminalCallbacks_fullBracket hn A B c hcycle ha hb hx hy H hclean hzRight hxz hyAxis hrow hurv hulv hpqAdj hpqAdj' hpq hpq' hRArc hLArc Q W hQW hchanging

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_automaticFullBracketCleanTwoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_automaticFullBracketCleanTwoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u z x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c hx hy).edges) :
-- imply
  ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p') (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2) (i j : Nat) (H : (hypercubicLattice 2).Walk ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i) ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j)) (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∈ c.support) (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∈ c.support), Q.support ⊆ W.support ∧ (∀ v ∈ Q.support, v = p ∨ v = p' ∨ v = q ∨ v = q' ∨ v ∈ rlc_pathVertices gamma'.1) ∧ (∀ v ∈ W.support, v = p ∨ v = p' ∨ v ∈ Q.support) ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ H.IsPath ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈ H.support ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∉ c.support ∧ H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support ∧ (∀ v ∈ H.support, v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∨ v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ (((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ul vl)) ∧ ((∃ v ∈ W.support, v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support) ∨ ((∃ v ∈ W.support, v ∈ (rlc_orderedContourArc c hx hy).support) ∧ ∃ v ∈ W.support, v ∈ (rlc_complementaryContourArc c hx hy).support))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_automaticFullBracketCleanTwoChannel hn hfaith A B hAright hAleft hBright hBleft hnoPair c hc hx hy hzRight hxPath hyPath qr ql hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpReach hpReach' hpShift hpShift' horder hxz hyAxis hRArc hLArc

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_unconditionalPhysicalTwoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_unconditionalPhysicalTwoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u z x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c hx hy).edges) :
-- imply
  ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p') (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2) (i j : Nat) (H : (hypercubicLattice 2).Walk ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i) ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j)) (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∈ c.support) (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∈ c.support), Q.support ⊆ W.support ∧ (∀ v ∈ Q.support, v = p ∨ v = p' ∨ v = q ∨ v = q' ∨ v ∈ rlc_pathVertices gamma'.1) ∧ (∀ v ∈ W.support, v = p ∨ v = p' ∨ v ∈ Q.support) ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ H.IsPath ∧ H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support ∧ (∀ v ∈ H.support, v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∨ v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ ((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ul vl)) ∧ RlcTwoChannelFullPhysicalRowOneSelectedPrimalFlankContactConclusion gamma gamma' c hx hy hzRight H W := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_unconditionalPhysicalTwoChannel hn hfaith A B hAright hAleft hBright hBleft hnoPair c hc hx hy hzRight hxPath hyPath qr ql hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpReach hpReach' hpShift hpShift' horder hxz hyAxis hRArc hLArc

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_cleanTwoChannel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_cleanTwoChannel_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hc : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ z ∈ H.support, z = a ∨ z = b ∨ (z ∉ c.support ∧ z ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hterminalNe : (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c ha hb).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c ha hb).edges)
  (hcycles : (H.append ((rlc_orderedContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c ha hb).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle) :
-- imply
  ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p') (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2), Q.support ⊆ W.support ∧ (∀ z ∈ Q.support, z = p ∨ z = p' ∨ z = q ∨ z = q' ∨ z ∈ rlc_pathVertices gamma'.1) ∧ (∀ z ∈ W.support, z = p ∨ z = p' ∨ z ∈ Q.support) ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ (((∃ e₀ ∈ W.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g)) ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ul vl)) ∧ ((∃ z ∈ W.support, z ∈ H.support) ∨ ((∃ z ∈ W.support, z ∈ (rlc_orderedContourArc c ha hb).support) ∧ ∃ z ∈ W.support, z ∈ (rlc_complementaryContourArc c ha hb).support))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_selectedPrimalFlank_cleanTwoChannel hn hfaith A B hAright hAleft hBright hBleft hnoPair c hc ha hb H hclean hxPath hyPath qr ql hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpReach hpReach' hpShift hpShift' horder hterminalNe hRArc hLArc hcycles

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_cleanSeparator_terminalResidue_or_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_cleanSeparator_terminalResidue_or_bridge_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u z x y ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hcycle : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl) :
-- imply
  ∃ (T : (hypercubicLattice 2).Walk vr vl) (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2) (i j : Nat) (H : (hypercubicLattice 2).Walk ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i) ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j)) (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∈ c.support) (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∈ c.support), (∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A), phb_doubleDualShift a = v) ∧ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ (s(f, g) ∈ T.edges ∨ (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalExactResidue gamma gamma' A B ul vl)) ∧ H.IsPath ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈ H.support ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∉ c.support ∧ H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support ∧ (∀ v ∈ H.support, v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∨ v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_cleanSeparator_terminalResidue_or_bridge hn hfaith A B hAright hAleft hBright hBleft hnoPair c hcycle hx hy hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_rowOneExactSourceSpliceEdgeResidue_cleanSeparatorContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOneExactSourceSpliceEdgeResidue_cleanSeparatorContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b ur vr ul vl p p' f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hres : RlcTwoChannelFullPhysicalRowOneExactSourceSpliceEdgeResidue gamma gamma' A B ur vr ul vl w f g) :
-- imply
  RlcTwoChannelFullPhysicalRowOneCleanExactSourceSpliceEdgeResidue gamma gamma' A B c H ur vr ul vl w f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOneExactSourceSpliceEdgeResidue_cleanSeparatorContact A B c hcycle ha hb H hclean w hres

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice_cleanSeparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice_cleanSeparator_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u z x y ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hcycle : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p') (T : (hypercubicLattice 2).Walk vr vl) (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2) (i j : Nat) (H : (hypercubicLattice 2).Walk ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i) ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j)) (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∈ c.support) (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∈ c.support), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ (∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) ∧ (∀ a ∈ w.support, phb_doubleDualShift a ∈ T.support) ∧ (∀ e ∈ w.edges, Sym2.map phb_doubleDualShift e ∈ T.edges) ∧ (∀ a ∈ T.support, a = vr ∨ a = ur ∨ a = ul ∨ a = vl ∨ ∃ b ∈ w.support, phb_doubleDualShift b = a) ∧ (∀ e ∈ T.edges, (∀ a ∈ e, a = vr ∨ a = ur ∨ a = phb_doubleDualShift p) ∨ (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e) ∨ ∀ a ∈ e, a = vl ∨ a = ul ∨ a = phb_doubleDualShift p') ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧ H.IsPath ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈ H.support ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∉ c.support ∧ H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support ∧ (∀ v ∈ H.support, v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∨ v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ RlcTwoChannelFullPhysicalRowOneCleanExactSourceSpliceEdgeResidue gamma gamma' A B c H ur vr ul vl w f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedExactSourceSplice_cleanSeparator hn hfaith A B hAright hAleft hBright hBleft hnoPair c hcycle hx hy hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {t v : Site 2}
-- given
  (hn : 0 < n)
  (ht : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect t))
  (hv : rlc_dualReflect v ∈ rlc_pathVertices gamma.1 ∨ rlc_dualReflect v ∈ rlc_pathVertices gamma'.1 ∨ v = rlc_dualReflect.symm (![-2 * n - 1, (gamma'.1.1 : Site 2) 1] : Site 2)) :
-- imply
  t ≠ v := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_exclusiveReflectedLeft_ne_rowOneBracketBoundaryContact hn ht hv

/--
[rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_ne_chordEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_ne_chordEndpoints_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur ul : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hcycle : c.IsCycle)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∈ c.support)
  (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∈ c.support) :
-- imply
  (ur ≠ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∧ ur ≠ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j) ∧ (ul ≠ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∧ ul ≠ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_ne_chordEndpoints hn c hcycle hzRight qr ql hrow hi hj

/--
[rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_not_mem_bracket](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_not_mem_bracket_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur ul : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hn : 0 < n)
  (hcycle : c.IsCycle)
  (hurC : ur ∈ c.support)
  (hulC : ul ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql) :
-- imply
  ur ∉ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support ∧ ul ∉ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_not_mem_bracket hn c hcycle hurC hulC hzRight hrow

/--
[rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_ne_bracketSubwalkEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_ne_bracketSubwalkEndpoints_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur vr ul vl a b : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hn : 0 < n)
  (hcycle : c.IsCycle)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support) :
-- imply
  (ur ≠ a ∧ ur ≠ b) ∧ (ul ≠ a ∧ ul ≠ b) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_reflectedLeftTerminals_ne_bracketSubwalkEndpoints hn c hcycle hzRight hrow hurv hulv H hHB

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_bracket_or_orderedArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_bracket_or_orderedArc_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hn : 0 < n)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c hx hy).edges) :
-- imply
  (∃ a ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support, a = p ∨ a = p' ∨ a = q ∨ a = q' ∨ a ∈ rlc_pathVertices gamma'.1) ∨ ∃ a ∈ (rlc_orderedContourArc c hx hy).support, a = p ∨ a = p' ∨ a = q ∨ a = q' ∨ a ∈ rlc_pathVertices gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_meets_bracket_or_orderedArc hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_meets_bracket_or_bothOriginalArcs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_meets_bracket_or_bothOriginalArcs_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
-- given
  (hn : 0 < n)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c hx hy).edges) :
-- imply
  ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p'), Q.support ⊆ W.support ∧ (∀ a ∈ Q.support, a = p ∨ a = p' ∨ a = q ∨ a = q' ∨ a ∈ rlc_pathVertices gamma'.1) ∧ (∀ a ∈ W.support, a = p ∨ a = p' ∨ a ∈ Q.support) ∧ ((∃ a ∈ W.support, a ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support) ∨ ((∃ a ∈ W.support, a ∈ (rlc_orderedContourArc c hx hy).support) ∧ ∃ a ∈ W.support, a ∈ (rlc_complementaryContourArc c hx hy).support)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_meets_bracket_or_bothOriginalArcs hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_indexedContact_or_bothOriginalArcs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_indexedContact_or_bothOriginalArcs_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c hx hy).edges)
  (hiLength : i ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hij : i ≤ j)
  (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length) :
-- imply
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight let H := rlc_walkIndexInterval B i j hiLength hij hjLength ∃ (Q : (hypercubicLattice 2).Walk q q') (W : (hypercubicLattice 2).Walk p p'), Q.support ⊆ W.support ∧ (∀ a ∈ Q.support, a = p ∨ a = p' ∨ a = q ∨ a = q' ∨ a ∈ rlc_pathVertices gamma'.1) ∧ (∀ a ∈ W.support, a = p ∨ a = p' ∨ a ∈ Q.support) ∧ ((∃ a ∈ W.support, a ∈ H.support) ∨ (∃ k : Nat, k < i ∧ B.getVert k ∈ W.support) ∨ (∃ k : Nat, j < k ∧ k ≤ B.length ∧ B.getVert k ∈ W.support) ∨ ((∃ a ∈ W.support, a ∈ (rlc_orderedContourArc c hx hy).support) ∧ ∃ a ∈ W.support, a ∈ (rlc_complementaryContourArc c hx hy).support)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_indexedContact_or_bothOriginalArcs hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc i j hiLength hij hjLength

/--
[rlc_twoChannelFullPhysical_boundary_exteriorEndpoint_of_reachableOrientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_exteriorEndpoint_of_reachableOrientation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g p q : Site 2}
-- given
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega) :
-- imply
  q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_exteriorEndpoint_of_reachableOrientation hfg hpq hpReach

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_vertexSideCases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_vertexSideCases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u p q p' q' v : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {Q : (hypercubicLattice 2).Walk q q'}
  {W : (hypercubicLattice 2).Walk p p'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hcycle : c.IsCycle)
  (hqOutside : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOutside' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hQprov : ∀ a ∈ Q.support, a = p ∨ a = p' ∨ a = q ∨ a = q' ∨ a ∈ rlc_pathVertices gamma'.1)
  (hWprov : ∀ a ∈ W.support, a = p ∨ a = p' ∨ a ∈ Q.support)
  (hvW : v ∈ W.support) :
-- imply
  v = p ∨ v = p' ∨ v ∈ c.support ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_selectedPrimalFlank_vertexSideCases hfaith A hAright hAleft c hcycle hqOutside hqOutside' Q W hQprov hWprov hvW

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_originalParity_indexedContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_originalParity_indexedContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c hx hy).edges)
  (hiLength : i ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hij : i ≤ j)
  (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length) :
-- imply
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight let H := rlc_walkIndexInterval B i j hiLength hij hjLength let P : Site 2 → Prop := fun a => a = p ∨ a = p' ∨ a = q ∨ a = q' ∨ a ∈ rlc_pathVertices gamma'.1 (∃ a ∈ H.support, P a) ∨ (∃ k : Nat, k < i ∧ P (B.getVert k)) ∨ (∃ k : Nat, j < k ∧ k ≤ B.length ∧ P (B.getVert k)) ∨ ∃ a ∈ (rlc_orderedContourArc c hx hy).support, P a := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_primalFlankWalk_originalParity_indexedContact hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc i j hiLength hij hjLength

/--
[rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b ur vr ul vl p p' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {T : (hypercubicLattice 2).Walk vr vl}
  {v : Site 2}
-- given
  (hcycle : c.IsCycle)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hwReach : ∀ z ∈ w.support, z ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hTprov : ∀ z ∈ T.support, z = vr ∨ z = ur ∨ z = ul ∨ z = vl ∨ ∃ r ∈ w.support, phb_doubleDualShift r = z)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hvH : v ∈ H.support)
  (hvT : v ∈ T.support) :
-- imply
  v = a ∨ v = b ∨ ∃ r ∈ w.support, phb_doubleDualShift r = v ∧ (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection c hcycle H hclean w T hwReach hTprov hurv hulv hvH hvT

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_support_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_support_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z v : Site 2}
-- given
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hv : v ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support) :
-- imply
  (∃ w ∈ rlc_pathVertices gamma.1, v = rlc_dualReflect.symm w) ∨ (∃ w ∈ (rlc_bookExteriorEndpointDetour gamma gamma').support, v = rlc_dualReflect.symm w) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, v = rlc_dualReflect.symm w := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_support_cases gamma gamma' hzRight hv

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_originalParity_HContact_or_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_originalParity_HContact_or_residue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c hx hy).edges)
  (hiLength : i ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hij : i ≤ j)
  (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length) :
-- imply
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight let H := rlc_walkIndexInterval B i j hiLength hij hjLength let P := RlcTwoChannelFullPhysicalRowOneOriginalParityContact gamma' p q p' q' (∃ a ∈ H.support, P a) ∨ RlcTwoChannelFullPhysicalRowOneOriginalParityIndexedContactResidue gamma gamma' c hx hy hzRight i j p q p' q' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_originalParity_HContact_or_residue hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc i j hiLength hij hjLength

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_originalParity_HContact_of_noResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_originalParity_HContact_of_noResidue_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z x y ur vr ul vl p q p' q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hc : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hurv : (hypercubicLattice 2).Adj ur vr)
  (hulv : (hypercubicLattice 2).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpqAdj : (hypercubicLattice 2).Adj p q)
  (hpqAdj' : (hypercubicLattice 2).Adj p' q')
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (horder : ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul))
  (hRArc : s(ur, vr) ∈ (rlc_orderedContourArc c hx hy).edges)
  (hLArc : s(ul, vl) ∈ (rlc_complementaryContourArc c hx hy).edges)
  (hiLength : i ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hij : i ≤ j)
  (hjLength : j ≤ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).length)
  (hresidue : ¬ RlcTwoChannelFullPhysicalRowOneOriginalParityIndexedContactResidue gamma gamma' c hx hy hzRight i j p q p' q') :
-- imply
  let B := rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight let H := rlc_walkIndexInterval B i j hiLength hij hjLength let P := RlcTwoChannelFullPhysicalRowOneOriginalParityContact gamma' p q p' q' ∃ a ∈ H.support, P a := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_originalParity_HContact_of_noResidue hn c hc hx hy hzRight hxz hyAxis hrow hurv hulv hpq hpq' hpqAdj hpqAdj' hpShift hpShift' horder hRArc hLArc i j hiLength hij hjLength hresidue

/--
[rlc_twoChannelFullPhysical_rowOneBracket_shiftedReach_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOneBracket_shiftedReach_cases_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {z a : Site 2}
-- given
  (hn : 0 < n)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (haBracket : phb_doubleDualShift a ∈ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support) :
-- imply
  (∃ w ∈ rlc_pathVertices gamma.1, a = rlc_flipX w) ∨ ∃ w ∈ rlc_pathVertices gamma'.1, a = rlc_flipX w := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOneBracket_shiftedReach_cases hn hzRight haReach haBracket

/--
[rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_classified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_classified_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z a b ur vr ul vl p p' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {T : (hypercubicLattice 2).Walk vr vl}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hcycle : c.IsCycle)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hwReach : ∀ r ∈ w.support, r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ r ∈ w.support, phb_doubleDualShift r = v)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hvH : v ∈ H.support)
  (hvT : v ∈ T.support) :
-- imply
  v = a ∨ v = b ∨ ∃ r ∈ w.support, phb_doubleDualShift r = v ∧ (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧ ((∃ q ∈ rlc_pathVertices gamma.1, r = rlc_flipX q) ∨ ∃ q ∈ rlc_pathVertices gamma'.1, r = rlc_flipX q) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_classified hn c hcycle hzRight H hHB hclean w T hwReach hTprov hurv hulv hvH hvT

/--
[rlc_twoChannelFullPhysical_reachable_reflectedLeft_intersection_or_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachable_reflectedLeft_intersection_or_exclusive_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {a w : Site 2}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hwLeft : w ∈ rlc_pathVertices gamma'.1)
  (haw : a = rlc_flipX w) :
-- imply
  a ∈ rlc_pathVertices gamma.1 ∨ RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' a := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachable_reflectedLeft_intersection_or_exclusive hfaith hno haReach hwLeft haw

/--
[rlc_bookRowOnePhysicalTraceNetworkBracket_axisSource_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_bookRowOnePhysicalTraceNetworkBracket_axisSource_not_mem_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {z : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
-- imply
  phb_doubleDualShift (gamma.1.1 : Site 2) ∉ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support := by
-- proof
  apply StatMech.Universality.rlc_bookRowOnePhysicalTraceNetworkBracket_axisSource_not_mem hn hfaith hzRight hzLeft

/--
[rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_exactLocations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_exactLocations_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z a b ur vr ul vl p p' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {T : (hypercubicLattice 2).Walk vr vl}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hcycle : c.IsCycle)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hwReach : ∀ r ∈ w.support, r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ r ∈ w.support, phb_doubleDualShift r = v)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hvH : v ∈ H.support)
  (hvT : v ∈ T.support) :
-- imply
  v = a ∨ v = b ∨ ∃ r ∈ w.support, phb_doubleDualShift r = v ∧ (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧ (RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' r ∨ (r ∈ rlc_pathVertices gamma.1 ∧ ∃ q ∈ rlc_pathVertices gamma'.1, r = rlc_flipX q) ∨ RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' r) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_exactLocations hn hfaith hno c hcycle hzRight hzLeft H hHB hclean w T hwReach hTprov hurv hulv hvH hvT

/--
[rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_rightArcBadLocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_rightArcBadLocation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z a b ur vr ul vl p p' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {T : (hypercubicLattice 2).Walk vr vl}
  {v : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hcycle : c.IsCycle)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hwReach : ∀ r ∈ w.support, r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ r ∈ w.support, phb_doubleDualShift r = v)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hvH : v ∈ H.support)
  (hvT : v ∈ T.support) :
-- imply
  v = a ∨ v = b ∨ ∃ r ∈ w.support, phb_doubleDualShift r = v ∧ (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧ RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' r := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_cleanSeparator_sourceSplice_intersection_rightArcBadLocation hn hfaith hno c hcycle hzRight hzLeft H hHB hclean w T hwReach hTprov hurv hulv hvH hvT

/--
[rlc_twoChannelFullPhysical_rowOne_cleanSeparator_shiftedSourceVertex_rightArcBadLocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_cleanSeparator_shiftedSourceVertex_rightArcBadLocation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z a b ur vr ul vl p p' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {T : (hypercubicLattice 2).Walk vr vl}
  {r : Site 2}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hcycle : c.IsCycle)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hwReach : ∀ r ∈ w.support, r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hwT : ∀ r ∈ w.support, phb_doubleDualShift r ∈ T.support)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ r ∈ w.support, phb_doubleDualShift r = v)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hrw : r ∈ w.support)
  (hrH : phb_doubleDualShift r ∈ H.support) :
-- imply
  phb_doubleDualShift r = a ∨ phb_doubleDualShift r = b ∨ ((r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧ RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' r) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_cleanSeparator_shiftedSourceVertex_rightArcBadLocation hn hfaith hno c hcycle hzRight hzLeft H hHB hclean w T hwReach hwT hTprov hurv hulv hrw hrH

/--
[rlc_twoChannelFullPhysical_rowOne_shiftedSourceSubwalk_insideOutside_rightArcBad_or_cycleContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_shiftedSourceSubwalk_insideOutside_rightArcBad_or_cycleContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u z a b ur vr ul vl p p' s t : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {T : (hypercubicLattice 2).Walk vr vl}
  {P : (hypercubicLattice 2).Walk s t}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hHB : H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))))
  (hwReach : ∀ r ∈ w.support, r ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hwT : ∀ r ∈ w.support, phb_doubleDualShift r ∈ T.support)
  (hTprov : ∀ v ∈ T.support, v = vr ∨ v = ur ∨ v = ul ∨ v = vl ∨ ∃ r ∈ w.support, phb_doubleDualShift r = v)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl)
  (hPprov : ∀ v ∈ P.support, ∃ r ∈ w.support, phb_doubleDualShift r = v)
  (hsInside : s ∈ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega))))
  (htOutside : t ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' omega)))) :
-- imply
  (∃ r ∈ w.support, phb_doubleDualShift r ∈ c.support) ∨ ∃ r ∈ w.support, (r ∈ c.support ∨ (![r 0 - 1, r 1] : Site 2) ∈ c.support) ∧ RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' r := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_shiftedSourceSubwalk_insideOutside_rightArcBad_or_cycleContact hn hfaith hno c hcycle ha hb hzRight hzLeft H hHB hclean w T hwReach hwT hTprov hurv hulv P hPprov hsInside htOutside

/--
[rlc_pathEdge_endpoint_mem_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_pathEdge_endpoint_mem_vertices_eq
  {a b c d : Int}
  {tau : RlcCrossingPath a b c d}
  {e : Sym2 (Site 2)}
  {z : Site 2}
-- given
  (he : e ∈ rlc_pathEdges tau)
  (hz : z ∈ e) :
-- imply
  z ∈ rlc_pathVertices tau := by
-- proof
  apply StatMech.Universality.rlc_pathEdge_endpoint_mem_vertices tau he hz

/--
[rlc_twoChannelFullPhysical_reachableWalk_open_source_or_rightTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reachableWalk_open_source_or_rightTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p p' : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
  {e : Sym2 (Site 2)}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hwReach : ∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (he : e ∈ w.edges)
  (hsourceOrTrace : (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = e) ∨ e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
-- imply
  (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = e) ∨ e ∈ rlc_pathEdges gamma.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reachableWalk_open_source_or_rightTrace hno w hwReach he hsourceOrTrace

/--
[rlc_twoChannelFullPhysical_planarEdge_source_or_originalTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_planarEdge_source_or_originalTrace_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (hlat : e ∈ (hypercubicLattice 2).edgeSet)
  (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma') :
-- imply
  (∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = e) ∨ e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_planarEdge_source_or_originalTrace gamma gamma' hlat hplanar

/--
[rlc_twoChannelFullPhysical_sourceMissing_trace_or_notPlanar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_sourceMissing_trace_or_notPlanar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hmissing : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) :
-- imply
  rlc_pimsEdgeEquiv (target.1.map Subtype.val) ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 ∨ rlc_pimsEdgeEquiv (target.1.map Subtype.val) ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_sourceMissing_trace_or_notPlanar target hmissing

/--
[rlc_twoChannelFullPhysical_shiftedSourceMissing_rightTraceContact_or_preimageNotPlanar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedSourceMissing_rightTraceContact_or_preimageNotPlanar_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p p' : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
  {e : Sym2 (Site 2)}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hwReach : ∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (he : e ∈ w.edges)
  (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
  (hmissing : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) :
-- imply
  (∃ z ∈ e, z ∈ rlc_pathVertices gamma.1) ∨ rlc_pimsEdgeEquiv (target.1.map Subtype.val) ∉ rlc_connectorCentralFacePlanarEdges gamma gamma' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedSourceMissing_rightTraceContact_or_preimageNotPlanar hno w hwReach he target htarget hmissing

/--
[rlc_pimsEdgeEquiv_flipXEdge_incidentNonopposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_flipXEdge_incidentNonopposite_eq
  {a b : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  ∃ z x y : Site 2, s(a, b) = s(z, x) ∧ rlc_pimsEdgeEquiv s(rlc_flipX a, rlc_flipX b) = s(z, y) ∧ (hypercubicLattice 2).Adj z x ∧ (hypercubicLattice 2).Adj z y ∧ x ≠ y ∧ ¬(x 0 + y 0 = 2 * z 0 ∧ x 1 + y 1 = 2 * z 1) := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_flipXEdge_incidentNonopposite hab

/--
[rlc_pimsEdgeEquiv_flipXEdge_notPlanar_wall_or_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_pimsEdgeEquiv_flipXEdge_notPlanar_wall_or_boundary_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {e : Sym2 (Site 2)}
-- given
  (hlat : e ∈ (hypercubicLattice 2).edgeSet)
  (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
  (hnotPlanar : rlc_pimsEdgeEquiv (Sym2.map rlc_flipX e) ∉ rlc_connectorCentralFacePlanarEdges gamma gamma') :
-- imply
  e ∈ rlc_connectorFourTraceEdges gamma gamma' ∨ ∃ z ∈ e, z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n := by
-- proof
  apply StatMech.Universality.rlc_pimsEdgeEquiv_flipXEdge_notPlanar_wall_or_boundary gamma gamma' hlat hplanar hnotPlanar

/--
[rlc_twoChannelFullPhysical_shiftedSourceMissing_location](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedSourceMissing_location_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p p' : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
  {e : Sym2 (Site 2)}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hwReach : ∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (he : e ∈ w.edges)
  (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
  (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
  (hmissing : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) :
-- imply
  (∃ z ∈ e, z ∈ rlc_pathVertices gamma.1) ∨ e ∈ rlc_connectorFourTraceEdges gamma gamma' ∨ ∃ z ∈ e, z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedSourceMissing_location hno w hwReach he hplanar target htarget hmissing

/--
[rlc_twoChannelFullPhysical_shiftedSourceMissing_exactLocation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedSourceMissing_exactLocation_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {p p' : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
  {e : Sym2 (Site 2)}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hwReach : ∀ z ∈ w.support, z ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (he : e ∈ w.edges)
  (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
  (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
  (hmissing : ¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) :
-- imply
  ∃ z ∈ e, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedSourceMissing_exactLocation hfaith hno w hwReach he hplanar target htarget hmissing

/--
[rlc_twoChannelFullPhysical_source_notAcross_staticCut_reachSet_extend](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_source_notAcross_staticCut_reachSet_extend_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {u v : RlcConnectorVertex n}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hsource : source.1 = s(u, v))
  (huReach : u.1 ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A source.1) :
-- imply
  v.1 ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_source_notAcross_staticCut_reachSet_extend A hAright hAleft source hsource huReach hnotCross

/--
[rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {a b : Site 2}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hab : (hypercubicLattice 2).Adj a b)
  (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hbReach : b ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX a, rlc_flipX b))
  (hphysical : physical.1 = target)
  (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_endpoints_reachable A hAright hAleft hab haReach hbReach target htarget physical hphysical hnotCross

/--
[rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noOutsideEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noOutsideEndpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {a b : Site 2}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hab : (hypercubicLattice 2).Adj a b)
  (haReach : a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hbReach : b ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX a, rlc_flipX b))
  (hphysical : physical.1 = target)
  (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  ¬∃ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noOutsideEndpoint A hAright hAleft hab haReach hbReach target htarget physical hphysical hnotCross

/--
[rlc_twoChannelFullPhysical_shiftedSourceEdge_status_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedSourceEdge_status_reachable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {p p' : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
  {e₀ : Sym2 (Site 2)}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hwReach : ∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (he₀ : e₀ ∈ w.edges)
  (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e₀)
  (hstatus : (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧ ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedSourceEdge_status_reachable A hAright hAleft w hwReach he₀ target htarget hstatus

/--
[rlc_twoChannelFullPhysical_shiftedSourceEdge_status_localized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedSourceEdge_status_localized_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {p p' : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
  {e : Sym2 (Site 2)}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hwReach : ∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (he : e ∈ w.edges)
  (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
  (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
  (hstatus : (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  ((∃ z ∈ e, z ∈ rlc_pathVertices gamma.1) ∨ e ∈ rlc_connectorFourTraceEdges gamma gamma' ∨ ∃ z ∈ e, z 0 = -2 * n ∨ z 0 = 2 * n ∨ z 1 = -n ∨ z 1 = n) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧ ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedSourceEdge_status_localized A hAright hAleft w hwReach he hplanar target htarget hstatus

/--
[rlc_twoChannelFullPhysical_shiftedSourceEdge_status_exactLocations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedSourceEdge_status_exactLocations_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {p p' : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
  {e : Sym2 (Site 2)}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hwReach : ∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (he : e ∈ w.edges)
  (hplanar : e ∈ rlc_connectorCentralFacePlanarEdges gamma gamma')
  (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
  (hstatus : (¬Nonempty (RlcTwoChannelAmbientSourceEdge gamma gamma' (rlc_pimsEdgeEquiv (target.1.map Subtype.val)))) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  (∃ z ∈ e, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧ ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedSourceEdge_status_exactLocations hfaith A hAright hAleft w hwReach he hplanar target htarget hstatus

/--
[rlc_twoChannelFullPhysical_rowOneCleanExactSourceSpliceEdgeResidue_localized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOneCleanExactSourceSpliceEdgeResidue_localized_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b ur vr ul vl p p' f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
-- given
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hwReach : ∀ z ∈ w.support, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hres : RlcTwoChannelFullPhysicalRowOneCleanExactSourceSpliceEdgeResidue gamma gamma' A B c H ur vr ul vl w f g) :
-- imply
  RlcTwoChannelFullPhysicalRowOneLocalizedExactSourceSpliceEdgeResidue gamma gamma' A B c H ur vr ul vl w f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOneCleanExactSourceSpliceEdgeResidue_localized hfaith A B hAright hAleft c H w hwReach hres

/--
[rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedLocalizedSourceSplice_cleanSeparator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedLocalizedSourceSplice_cleanSeparator_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u z x y ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hfaith : RlcBookFaithfulTracePair gamma gamma')
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hBright : ∀ x, rlc_connectorOnRight gamma x → x ∈ B)
  (hBleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ B)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hcycle : c.IsCycle)
  (hx : x ∈ c.support)
  (hy : y ∈ c.support)
  (hzRight : z ∈ rlc_pathVertices gamma.1)
  (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
  (hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1)
  (hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1)
  (hxz : rlc_dualReflect x = z)
  (hyAxis : rlc_dualReflect y = (gamma'.1.2.1 : Site 2))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p') (T : (hypercubicLattice 2).Walk vr vl) (V : (hypercubicLattice 2).Walk (rlc_dualReflect.symm (gamma.1.1 : Site 2)) (rlc_dualReflect.symm (gamma'.1.2.1 : Site 2))) (f g : Site 2) (i j : Nat) (H : (hypercubicLattice 2).Walk ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i) ((rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j)) (hi : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∈ c.support) (hj : (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∈ c.support), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ (∀ a ∈ w.support, a ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) ∧ (∀ a ∈ w.support, phb_doubleDualShift a ∈ T.support) ∧ (∀ e ∈ w.edges, Sym2.map phb_doubleDualShift e ∈ T.edges) ∧ (∀ a ∈ T.support, a = vr ∨ a = ur ∨ a = ul ∨ a = vl ∨ ∃ b ∈ w.support, phb_doubleDualShift b = a) ∧ (∀ e ∈ T.edges, (∀ a ∈ e, a = vr ∨ a = ur ∨ a = phb_doubleDualShift p) ∨ (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = e) ∨ ∀ a ∈ e, a = vl ∨ a = ul ∨ a = phb_doubleDualShift p') ∧ s(f, g) ∈ V.edges ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g) ∧ ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ur) < ((rlc_ambientCrossingWalk gamma'.1).map rlc_flipXLatticeHom).support.idxOf (rlc_dualReflect ul) ∧ H.IsPath ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∈ H.support ∧ rlc_dualReflect.symm (![(2 * n + 2), n + 2] : Site 2) ∉ c.support ∧ H.support ⊆ (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).support ∧ (∀ v ∈ H.support, v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert i ∨ v = (rlc_bookRowOnePhysicalTraceNetworkBracket gamma gamma' hzRight).getVert j ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))))) ∧ (H.append ((rlc_orderedContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ (H.append ((rlc_complementaryContourArc c hi hj).mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)))).reverse).IsCycle ∧ RlcTwoChannelFullPhysicalRowOneLocalizedExactSourceSpliceEdgeResidue gamma gamma' A B c H ur vr ul vl w f g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_wallFamilyRowOne_orderedLocalizedSourceSplice_cleanSeparator hn hfaith A B hAright hAleft hBright hBleft hnoPair c hcycle hx hy hzRight hzLeft hxPath hyPath qr ql hxz hyAxis hrow hurv hulv

/--
[rlc_twoChannelFullPhysical_rowOne_reachableShift_tether_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOne_reachableShift_tether_terminal_eq
  {f g ur vr ul vl p p' : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (htether : ((s(f, g) = s(vr, phb_doubleDualShift p) ∨ s(f, g) = s(ur, phb_doubleDualShift p)) ∨ (s(f, g) = s(vl, phb_doubleDualShift p') ∨ s(f, g) = s(ul, phb_doubleDualShift p')))) :
-- imply
  s(f, g) = s(ur, vr) ∨ s(f, g) = s(ul, vl) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOne_reachableShift_tether_terminal hfg hpShift hpShift' htether

/--
[rlc_twoChannelFullPhysical_noPair_rowOne_cleanSeparator_terminalBranch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_rowOne_cleanSeparator_terminalBranch_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b x y ur vr ul vl f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
-- given
  (hn : 0 < n)
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g))
  (hterminal : s(f, g) = s(ur, vr) ∨ s(f, g) = s(ul, vl)) :
-- imply
  (s(f, g) = s(ur, vr) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ur vr) ∨ (s(f, g) = s(ul, vl) ∧ RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H ul vl) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_rowOne_cleanSeparator_terminalBranch hn A B hAright hAleft hnoPair c hcycle ha hb H hclean qr ql hrow hurv hulv hcross hterminal

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b f g p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hterminal : RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H f g) :
-- imply
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_reflectedPathEdges gamma'.1) ∨ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧ (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧ sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) p q) ∨ p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧ (q ∈ H.support ∨ p ∈ c.support ∨ q ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource A B c H ha hb hpq hpReach hqOut hterminal

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_chord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_chord_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b f g p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (havoid : p ∉ c.support ∧ q ∉ c.support)
  (hterminal : RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H f g) :
-- imply
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_reflectedPathEdges gamma'.1) ∨ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧ (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧ sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ (((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p) ∧ ∃ z : Site 2, (hypercubicLattice 2).Adj p z ∧ rlc_twoChannelFullAmbientConfig gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) s(p, z) = true ∧ ((∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, z)) ∨ (s(p, z) ∉ rlc_connectorFourTraceEdges gamma gamma' ∧ z 0 + q 0 = 2 * p 0 ∧ z 1 + q 1 = 2 * p 1 ∧ ∀ y : Site 2, (hypercubicLattice 2).Adj p y → y ≠ z → y ≠ q → ∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = s(p, y)))) ∨ p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧ q ∈ H.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_chord A B c H ha hb hpq hpReach hqOut havoid hterminal

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminal_nonChord_forces_cycleEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminal_nonChord_forces_cycleEndpoint_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b f g p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hterminal : RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H f g)
  (hnoTargetBad : ¬(( ¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_reflectedPathEdges gamma'.1))
  (hqH : q ∉ H.support) :
-- imply
  p ∈ c.support ∨ q ∈ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminal_nonChord_forces_cycleEndpoint A B c H ha hb hpq hpReach hqOut hterminal hnoTargetBad hqH

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminal_reachableSource_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminal_reachableSource_incidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {f g p q : Site 2}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f))
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega) :
-- imply
  phb_doubleDualShift p = g ∨ p = f ∨ p = g := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminal_reachableSource_incidence hno hfg hfExclusive hpq hpReach

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminal_literalSourceEdge_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminal_literalSourceEdge_geometry_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {f g p q : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f))
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpFace : p = f ∨ p = g) :
-- imply
  ∃ w ∈ rlc_pathVertices gamma'.1, (p = f ∧ phb_doubleDualShift q = g ∧ (q = ![w 0 - 1, w 1] ∨ q = ![w 0, w 1 - 1])) ∨ (p = g ∧ phb_doubleDualShift q = f ∧ q = w ∧ (p = ![w 0 - 1, w 1] ∨ p = ![w 0, w 1 - 1])) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminal_literalSourceEdge_geometry hfg hfExclusive hpq hpFace

/--
[rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource_incidence_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b f g p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hfExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect f))
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hterminal : RlcTwoChannelFullPhysicalReflectedLeftTerminalCleanSeparatorContact gamma gamma' A B c H f g) :
-- imply
  ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' f g) ∧ s(rlc_dualReflect f, rlc_dualReflect g) ∉ rlc_reflectedPathEdges gamma'.1) ∨ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s(rlc_dualReflect f, rlc_dualReflect g) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧ (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' f g) ∧ sharedPrimalEdge f g = s(p, q) ∧ (hypercubicLattice 2).Adj p q ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' p ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) p q) ∨ p 0 = -2 * n ∨ p 1 = -n ∨ p 1 = n) ∧ (phb_doubleDualShift p = g ∨ p = f ∨ p = g) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_reflectedLeftTerminalCleanSeparatorContact_identifySource_incidence A B hno c H ha hb hfg hfExclusive hpq hpReach hqOut hterminal

/--
[rlc_twoChannelFullPhysical_rowOneLocalizedExactSourceSpliceEdgeResidue_terminalBranches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOneLocalizedExactSourceSpliceEdgeResidue_terminalBranches_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b ur vr ul vl p q p' q' f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hurExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ur))
  (hulExclusive : RlcTwoChannelFullPhysicalExclusiveReflectedLeftLocation gamma gamma' (rlc_dualReflect ul))
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hres : RlcTwoChannelFullPhysicalRowOneLocalizedExactSourceSpliceEdgeResidue gamma gamma' A B c H ur vr ul vl w f g) :
-- imply
  let terminalBranch := fun t v r s => ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' t v) ∧ s(rlc_dualReflect t, rlc_dualReflect v) ∉ rlc_reflectedPathEdges gamma'.1) ∨ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s(rlc_dualReflect t, rlc_dualReflect v) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧ (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' t v) ∧ sharedPrimalEdge t v = s(r, s) ∧ (hypercubicLattice 2).Adj r s ∧ r ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ s ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' r ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) r s) ∨ r 0 = -2 * n ∨ r 1 = -n ∨ r 1 = n) ∧ ∃ z ∈ rlc_pathVertices gamma'.1, (r = t ∧ phb_doubleDualShift s = v ∧ (s = ![z 0 - 1, z 1] ∨ s = ![z 0, z 1 - 1])) ∨ (r = v ∧ phb_doubleDualShift s = t ∧ s = z ∧ (r = ![z 0 - 1, z 1] ∨ r = ![z 0, z 1 - 1])) (((s(f, g) = s(ur, vr) ∧ terminalBranch ur vr p q) ∨ (s(f, g) = s(ul, vl) ∧ terminalBranch ul vl p' q')) ∨ (s(f, g) = s(vr, phb_doubleDualShift p) ∨ s(f, g) = s(ur, phb_doubleDualShift p)) ∨ (∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g) ∧ rlc_twoChannelFullAmbientConfig gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) e₀ = true ∧ ((∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = e₀) ∨ e₀ ∈ rlc_pathEdges gamma.1) ∧ e₀ ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) (Sym2.map rlc_flipX e₀) ∧ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = Sym2.map rlc_flipX e₀ ∧ ((∃ z ∈ e₀, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧ ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))) ∨ (s(f, g) = s(vl, phb_doubleDualShift p') ∨ s(f, g) = s(ul, phb_doubleDualShift p'))) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOneLocalizedExactSourceSpliceEdgeResidue_terminalBranches A B hno c H w ha hb hurv hulv hurExclusive hulExclusive hpq hpq' hpReach hpReach' hqOut hqOut' hres

/--
[rlc_twoChannelFullPhysical_rowOneLocalizedExactSourceSpliceEdgeResidue_tetherFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_rowOneLocalizedExactSourceSpliceEdgeResidue_tetherFree_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b x y ur vr ul vl p q p' q' f g : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)).Walk y ul}
  {w : (hypercubicLattice 2).Walk p p'}
-- given
  (hn : 0 < n)
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) qr ql)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Adj ul vl)
  (hpq : sharedPrimalEdge ur vr = s(p, q))
  (hpq' : sharedPrimalEdge ul vl = s(p', q'))
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hpShift : phb_doubleDualShift p = vr)
  (hpShift' : phb_doubleDualShift p' = vl)
  (hfg : (hypercubicLattice 2).Adj f g)
  (hcross : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) s(rlc_dualReflect f, rlc_dualReflect g))
  (hres : RlcTwoChannelFullPhysicalRowOneLocalizedExactSourceSpliceEdgeResidue gamma gamma' A B c H ur vr ul vl w f g) :
-- imply
  let terminalBranch := fun t v r s => ((¬RlcTwoChannelFullPhysicalTargetCarrierGeometry gamma gamma' t v) ∧ s(rlc_dualReflect t, rlc_dualReflect v) ∉ rlc_reflectedPathEdges gamma'.1) ∨ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = s(rlc_dualReflect t, rlc_dualReflect v) ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1 ∧ (¬RlcTwoChannelFullPhysicalSourceCarrierGeometry gamma gamma' t v) ∧ sharedPrimalEdge t v = s(r, s) ∧ (hypercubicLattice 2).Adj r s ∧ r ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ s ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ ((RlcTwoChannelFullPhysicalExclusiveReflectedRightLocation gamma gamma' r ∧ RlcTwoChannelFullPhysicalExclusiveReflectedRightSourceTraceResidue gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) r s) ∨ r 0 = -2 * n ∨ r 1 = -n ∨ r 1 = n) ∧ (phb_doubleDualShift r = v ∨ r = t ∨ r = v) let shiftedSourceBranch := ∃ e₀ ∈ w.edges, Sym2.map phb_doubleDualShift e₀ = s(f, g) ∧ rlc_twoChannelFullAmbientConfig gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) e₀ = true ∧ ((∃ source : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, source.1.map Subtype.val = e₀) ∨ e₀ ∈ rlc_pathEdges gamma.1) ∧ e₀ ∈ rlc_connectorCentralFacePlanarEdges gamma gamma' ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) (Sym2.map rlc_flipX e₀) ∧ ∃ target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet, target.1.map Subtype.val = Sym2.map rlc_flipX e₀ ∧ (((∃ z ∈ e₀, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z)) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧ ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) (s(f, g) = s(ur, vr) ∧ terminalBranch ur vr p q) ∨ (s(f, g) = s(ul, vl) ∧ terminalBranch ul vl p' q') ∨ shiftedSourceBranch := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_rowOneLocalizedExactSourceSpliceEdgeResidue_tetherFree hn A B hAright hAleft hnoPair c hcycle ha hb H hclean qr ql hrow hurv hulv hpq hpq' hpReach hpReach' hqOut hqOut' hpShift hpShift' w hfg hcross hres

/--
[rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noSeparatorAvoidingExteriorReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noSeparatorAvoidingExteriorReroute_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u a b x y : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hxy : (hypercubicLattice 2).Adj x y)
  (hxReach : x ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hyReach : y ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target)
  (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  ∀ r ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, ¬∃ (t : Site 2) (P : (hypercubicLattice 2).Walk r t), t ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) ∧ (∀ z ∈ P.support, z ∉ c.support) ∧ ∀ z ∈ P.support, z ∉ H.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_notAcross_source_noSeparatorAvoidingExteriorReroute A hAright hAleft c hcycle ha hb H hxy hxReach hyReach target htarget physical hphysical hnotCross

/--
[rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalPrefixReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalPrefixReroute_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p p' x y q : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hxy : s(x, y) ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target) :
-- imply
  ∃ (z : Site 2) (hzW : z ∈ w.support), z ∈ s(x, y) ∧ ∃ r ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, (hypercubicLattice 2).Adj z r ∧ ∃ P : (hypercubicLattice 2).Walk r q, ∀ v ∈ P.support, v = q ∨ v ∈ (w.takeUntil z hzW).support ∨ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalPrefixReroute w hxy hpq target htarget physical hphysical

/--
[rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalReroute_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {p p' x y q : Site 2}
  {w : (hypercubicLattice 2).Walk p p'}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hxy : s(x, y) ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target) :
-- imply
  ∃ r ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, ∃ P : (hypercubicLattice 2).Walk r q, ∀ v ∈ P.support, v = q ∨ v ∈ w.support ∨ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_pairedSource_to_terminalReroute w hxy hpq target htarget physical hphysical

/--
[rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalReroute_cleanContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalReroute_cleanContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u a b p p' x y q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hwReach : ∀ v ∈ w.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hxy : s(x, y) ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target)
  (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  (q ∈ c.support ∨ q ∈ H.support) ∨ ∃ v : Site 2, (v ∈ w.support ∨ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val) ∧ v ∈ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalReroute_cleanContact A hAright hAleft c hcycle ha hb H hclean w hwReach hxy hpq hqOut target htarget physical hphysical hnotCross

/--
[rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalPrefixReroute_cleanContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalPrefixReroute_cleanContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u a b p p' x y q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hwReach : ∀ v ∈ w.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hxy : s(x, y) ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target)
  (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  (q ∈ c.support ∨ q ∈ H.support) ∨ ∃ (z : Site 2) (hzW : z ∈ w.support), z ∈ s(x, y) ∧ ((∃ v ∈ (w.takeUntil z hzW).support, v ∈ c.support) ∨ ∃ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, v ∈ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_terminalPrefixReroute_cleanContact A hAright hAleft c hcycle ha hb H hclean w hwReach hxy hpq hqOut target htarget physical hphysical hnotCross

/--
[rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalPrefixReroute_cleanContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalPrefixReroute_cleanContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u a b p p' x y q q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hwReach : ∀ v ∈ w.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hxy : s(x, y) ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target)
  (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  ((q ∈ c.support ∨ q ∈ H.support) ∨ ∃ (z : Site 2) (hzW : z ∈ w.support), z ∈ s(x, y) ∧ ((∃ v ∈ (w.takeUntil z hzW).support, v ∈ c.support) ∨ ∃ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, v ∈ c.support)) ∧ ((q' ∈ c.support ∨ q' ∈ H.support) ∨ ∃ (z : Site 2) (hzW : z ∈ w.reverse.support), z ∈ s(x, y) ∧ ((∃ v ∈ (w.reverse.takeUntil z hzW).support, v ∈ c.support) ∨ ∃ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, v ∈ c.support)) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalPrefixReroute_cleanContacts A hAright hAleft c hcycle ha hb H hclean w hwReach hxy hpq hpq' hqOut hqOut' target htarget physical hphysical hnotCross

/--
[rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_contactInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_contactInterval_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u a b p p' x y q q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hwReach : ∀ v ∈ w.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hxy : s(x, y) ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target)
  (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  (q ∈ c.support ∨ q ∈ H.support) ∨ (q' ∈ c.support ∨ q' ∈ H.support) ∨ (∃ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, v ∈ c.support) ∨ (∃ z ∈ s(x, y), z ∈ c.support) ∨ ∃ k i j : Nat, k < w.length ∧ s(w.getVert k, w.getVert (k + 1)) = s(x, y) ∧ i < k ∧ k + 1 < j ∧ j ≤ w.length ∧ w.getVert i ∈ c.support ∧ w.getVert j ∈ c.support ∧ ∀ l : Nat, i < l → l < j → w.getVert l ∉ c.support := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_contactInterval A hAright hAleft c hcycle ha hb H hclean w hwReach hxy hpq hpq' hqOut hqOut' target htarget physical hphysical hnotCross

/--
[rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_contactInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_contactInterval_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b p p' x y q q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hwReach : ∀ v ∈ w.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hxy : s(x, y) ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target)
  (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) (target.1.map Subtype.val)) :
-- imply
  (¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) ∧ ((q ∈ c.support ∨ q ∈ H.support) ∨ (q' ∈ c.support ∨ q' ∈ H.support) ∨ (∃ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, v ∈ c.support) ∨ (∃ z ∈ s(x, y), z ∈ c.support) ∨ ∃ k i j : Nat, k < w.length ∧ s(w.getVert k, w.getVert (k + 1)) = s(x, y) ∧ i < k ∧ k + 1 < j ∧ j ≤ w.length ∧ w.getVert i ∈ c.support ∧ w.getVert j ∈ c.support ∧ ∀ l : Nat, i < l → l < j → w.getVert l ∉ c.support) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_contactInterval A B hAright hAleft hnoPair c hcycle ha hb H hclean w hwReach hxy hpq hpq' hqOut hqOut' target htarget physical hphysical hcrossB

/--
[rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_reachableContactInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_reachableContactInterval_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b p p' x y q q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hwReach : ∀ v ∈ w.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hxy : s(x, y) ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target)
  (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) (target.1.map Subtype.val)) :
-- imply
  let Reach := rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) (¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) ∧ ((q ∈ c.support ∨ q ∈ H.support) ∨ (q' ∈ c.support ∨ q' ∈ H.support) ∨ (∃ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, v ∈ c.support ∧ v ∈ Reach) ∨ (∃ z ∈ s(x, y), z ∈ c.support ∧ z ∈ Reach) ∨ ∃ k i j : Nat, k < w.length ∧ s(w.getVert k, w.getVert (k + 1)) = s(x, y) ∧ i < k ∧ k + 1 < j ∧ j ≤ w.length ∧ w.getVert i ∈ c.support ∧ w.getVert j ∈ c.support ∧ (∀ l : Nat, i < l → l < j → w.getVert l ∉ c.support) ∧ ∀ l : Nat, i ≤ l → l ≤ j → w.getVert l ∈ Reach) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_noPair_crossingTarget_pairedSource_reachableContactInterval A B hAright hAleft hnoPair c hcycle ha hb H hclean w hwReach hxy hpq hpq' hqOut hqOut' target htarget physical hphysical hcrossB

/--
[rlc_twoChannelFullPhysical_shiftedSourceEdge_status_twoCut_reachableContactInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedSourceEdge_status_twoCut_reachableContactInterval_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A B : Set (RlcConnectorVertex n)}
  {u a b p p' q q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {e : Sym2 (Site 2)}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hnoPair : ¬∃ target : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge target).1 ∧ rlc_twoChannelFullPhysicalEdgeCrossesCut B target.1.1)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hwReach : ∀ v ∈ w.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (he : e ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
  (hcrossB : rlc_twoChannelFullPhysicalEdgeCrossesCut (rlc_twoChannelFullPhysicalLiftVertexCut B) (target.1.map Subtype.val))
  (hstatus : (∃ z ∈ e, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧ ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) :
-- imply
  let Reach := rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A) let Classified := fun physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' => (q ∈ c.support ∨ q ∈ H.support) ∨ (q' ∈ c.support ∨ q' ∈ H.support) ∨ (∃ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, v ∈ c.support ∧ v ∈ Reach) ∨ (∃ z ∈ e, z ∈ c.support ∧ z ∈ Reach) ∨ ∃ k i j : Nat, k < w.length ∧ s(w.getVert k, w.getVert (k + 1)) = e ∧ i < k ∧ k + 1 < j ∧ j ≤ w.length ∧ w.getVert i ∈ c.support ∧ w.getVert j ∈ c.support ∧ (∀ l : Nat, i < l → l < j → w.getVert l ∉ c.support) ∧ ∀ l : Nat, i ≤ l → l ≤ j → w.getVert l ∈ Reach (∃ z ∈ e, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧ (∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ Reach) ∧ Classified physical := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedSourceEdge_status_twoCut_reachableContactInterval A B hAright hAleft hnoPair c hcycle ha hb H hclean w hwReach he hpq hpq' hqOut hqOut' target htarget hcrossB hstatus

/--
[rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_cleanContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_cleanContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u a b p p' x y q q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
  {physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma'}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hwReach : ∀ v ∈ w.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hxy : s(x, y) ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = s(rlc_flipX x, rlc_flipX y))
  (hphysical : physical.1 = target)
  (hnotCross : ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1) :
-- imply
  let Contact := fun t : Site 2 => (t ∈ c.support ∨ t ∈ H.support) ∨ ∃ v : Site 2, (v ∈ w.support ∨ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val) ∧ v ∈ c.support Contact q ∧ Contact q' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedTarget_notAcross_pairedSource_twoTerminalReroute_cleanContacts A hAright hAleft c hcycle ha hb H hclean w hwReach hxy hpq hpq' hqOut hqOut' target htarget physical hphysical hnotCross

/--
[rlc_twoChannelFullPhysical_shiftedSourceEdge_status_rightArcBad_or_twoTerminalContacts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_shiftedSourceEdge_status_rightArcBad_or_twoTerminalContacts_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {A : Set (RlcConnectorVertex n)}
  {u a b p p' q q' : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {w : (hypercubicLattice 2).Walk p p'}
  {e : Sym2 (Site 2)}
  {target : (rlc_connectorTwoChannelGraph gamma gamma').edgeSet}
-- given
  (hAright : ∀ x, rlc_connectorOnRight gamma x → x ∈ A)
  (hAleft : ∀ y, rlc_connectorOnLeft gamma' y → y ∉ A)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hclean : ∀ v ∈ H.support, v = a ∨ v = b ∨ (v ∉ c.support ∧ v ∉ jec_leftRegion (c.mapLe (faceBoundaryGraph_le (rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))))))
  (hwReach : ∀ v ∈ w.support, v ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (he : e ∈ w.edges)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hqOut : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (hqOut' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A))
  (htarget : target.1.map Subtype.val = Sym2.map rlc_flipX e)
  (hstatus : (∃ z ∈ e, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧ ∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) :
-- imply
  let Contact := fun physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma' => fun t : Site 2 => (t ∈ c.support ∨ t ∈ H.support) ∨ ∃ v : Site 2, (v ∈ w.support ∨ v ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val) ∧ v ∈ c.support (∃ z ∈ e, RlcTwoChannelFullPhysicalRightArcBadLocation gamma gamma' z) ∨ ∃ physical : RlcTwoChannelFullPhysicalTargetEdge gamma gamma', physical.1 = target ∧ ¬rlc_twoChannelFullPhysicalEdgeCrossesCut A (rlc_twoChannelFullPhysicalSourceEdge physical).1 ∧ (∀ z ∈ (rlc_twoChannelFullPhysicalSourceEdge physical).1.map Subtype.val, z ∈ rlc_twoChannelFullReachSet gamma gamma' (rlc_twoChannelFullPhysicalCutInteriorConfig gamma gamma' A)) ∧ Contact physical q ∧ Contact physical q' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_shiftedSourceEdge_status_rightArcBad_or_twoTerminalContacts A hAright hAleft c hcycle ha hb H hclean w hwReach he hpq hpq' hqOut hqOut' target htarget hstatus

/--
[rlc_twoChannelFullPhysical_insideOutside_shiftedEndpointPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_insideOutside_shiftedEndpointPlacement_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOutside : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  RlcTwoChannelFullPhysicalShiftedEndpointPlacement gamma gamma' omega c p q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_insideOutside_shiftedEndpointPlacement c hcycle hpReach hqOutside

/--
[rlc_twoChannelFullPhysical_boundary_twoTerminal_shiftedEndpointPlacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_twoTerminal_shiftedEndpointPlacement_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u ur vr ul vl : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (hurv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ur vr)
  (hulv : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj ul vl) :
-- imply
  ∃ (p q p' q' : Site 2) (w : (hypercubicLattice 2).Walk p p'), sharedPrimalEdge ur vr = s(p, q) ∧ sharedPrimalEdge ul vl = s(p', q') ∧ (hypercubicLattice 2).Adj p q ∧ (hypercubicLattice 2).Adj p' q' ∧ p ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega ∧ q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega ∧ (∀ z ∈ w.support, z ∈ rlc_twoChannelFullReachSet gamma gamma' omega) ∧ RlcTwoChannelFullPhysicalShiftedEndpointPlacement gamma gamma' omega c p q ∧ RlcTwoChannelFullPhysicalShiftedEndpointPlacement gamma gamma' omega c p' q' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_twoTerminal_shiftedEndpointPlacement c hcycle hurv hulv

/--
[rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_meetsChord_or_tetherContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_meetsChord_or_tetherContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOutside : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega) :
-- imply
  (phb_doubleDualShift p ∈ H.support ∨ phb_doubleDualShift q ∈ H.support) ∨ ∃ z ∈ c.support, z = p ∨ z = ![p 0 - 1, p 1] ∨ z = phb_doubleDualShift p ∨ z = q ∨ z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_meetsChord_or_tetherContact c hcycle ha hb H hpq hpReach hqOutside

/--
[rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_HinterT_or_tetherContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_HinterT_or_tetherContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u a b p q s t : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {T : (hypercubicLattice 2).Walk s t}
-- given
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOutside : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hpT : phb_doubleDualShift p ∈ T.support)
  (hqT : phb_doubleDualShift q ∈ T.support) :
-- imply
  (∃ v ∈ H.support, v ∈ T.support) ∨ ∃ z ∈ c.support, z = p ∨ z = ![p 0 - 1, p 1] ∨ z = phb_doubleDualShift p ∨ z = q ∨ z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_insideOutside_shiftedEdge_HinterT_or_tetherContact c hcycle ha hb H T hpq hpReach hqOutside hpT hqT

/--
[rlc_twoChannelFullPhysical_boundary_shiftedEndpoint_tetherContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_boundary_shiftedEndpoint_tetherContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {u f g p q : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
-- given
  (hcycle : c.IsCycle)
  (hfg : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Adj f g)
  (hpq : sharedPrimalEdge f g = s(p, q))
  (hpqAdj : (hypercubicLattice 2).Adj p q) :
-- imply
  ∃ z ∈ c.support, z = p ∨ z = ![p 0 - 1, p 1] ∨ z = phb_doubleDualShift p ∨ z = q ∨ z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_boundary_shiftedEndpoint_tetherContact c hcycle hfg hpq hpqAdj

/--
[rlc_twoChannelFullPhysical_wallFamilyRowOne_exteriorIncidence_HinterT_or_tetherContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean)
-/
@[path]
private lemma rlc_twoChannelFullPhysical_wallFamilyRowOne_exteriorIncidence_HinterT_or_tetherContact_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {omega : RlcTwoChannelEdgeConfig gamma gamma'}
  {x y ur vr ul vl p q p' q' : Site 2}
  {qr : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk x ur}
  {ql : (rlc_twoChannelFullPhysicalGoodBoundaryGraph gamma gamma' omega).Walk y ul}
  {u a b s t : Site 2}
  {c : (faceBoundaryGraph (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u}
  {H : (hypercubicLattice 2).Walk a b}
  {T : (hypercubicLattice 2).Walk s t}
-- given
  (hno : rlc_twoChannelEdgeConfigExtend gamma gamma' omega ∉ rlc_finiteTwoChannelConnectorEvent gamma gamma')
  (hrow : RlcTwoChannelFullPhysicalTwoArcWallTerminalFamilyRowOne gamma gamma' omega qr ql)
  (hcycle : c.IsCycle)
  (ha : a ∈ c.support)
  (hb : b ∈ c.support)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hpq' : (hypercubicLattice 2).Adj p' q')
  (hpReach : p ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hpReach' : p' ∈ rlc_twoChannelFullReachSet gamma gamma' omega)
  (hqOutside : q ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hqOutside' : q' ∉ rlc_twoChannelFullFilledReachSet gamma gamma' omega)
  (hincR : phb_doubleDualShift p ∈ s(ur, vr) ∨ phb_doubleDualShift q ∈ s(ur, vr))
  (hincL : phb_doubleDualShift p' ∈ s(ul, vl) ∨ phb_doubleDualShift q' ∈ s(ul, vl))
  (hpT : phb_doubleDualShift p ∈ T.support)
  (hpT' : phb_doubleDualShift p' ∈ T.support)
  (hqT : phb_doubleDualShift q ∈ s(ur, vr) → phb_doubleDualShift q ∈ T.support)
  (hqT' : phb_doubleDualShift q' ∈ s(ul, vl) → phb_doubleDualShift q' ∈ T.support) :
-- imply
  (phb_doubleDualShift p = vr ∧ phb_doubleDualShift p' = vl) ∨ (∃ v ∈ H.support, v ∈ T.support) ∨ (∃ z ∈ c.support, z = p ∨ z = ![p 0 - 1, p 1] ∨ z = phb_doubleDualShift p ∨ z = q ∨ z = ![q 0 - 1, q 1] ∨ z = phb_doubleDualShift q) ∨ ∃ z ∈ c.support, z = p' ∨ z = ![p' 0 - 1, p' 1] ∨ z = phb_doubleDualShift p' ∨ z = q' ∨ z = ![q' 0 - 1, q' 1] ∨ z = phb_doubleDualShift q' := by
-- proof
  apply StatMech.Universality.rlc_twoChannelFullPhysical_wallFamilyRowOne_exteriorIncidence_HinterT_or_tetherContact hno hrow c hcycle ha hb H T hpq hpq' hpReach hpReach' hqOutside hqOutside' hincR hincL hpT hpT' hqT hqT'


-- created on 2026-10-23

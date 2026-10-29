import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveActualCarrierContainment
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealMiddle_subset_outgoingParameterCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma idealMiddle_subset_outgoingParameterCarrier_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealMiddleClosedEdge i q even ⊆ patch.outgoingParameterCarrier i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddle_subset_outgoingParameterCarrier patch i q even

/--
[KWAdaptivePatchedData.idealMiddle_subset_incomingParameterCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma idealMiddle_subset_incomingParameterCarrier_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealMiddleClosedEdge i q even ⊆ patch.incomingParameterCarrier i := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddle_subset_incomingParameterCarrier patch i q even

/--
[KWAdaptivePatchedData.outgoingParameterCarrier_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma outgoingParameterCarrier_isCompact_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  IsCompact (patch.outgoingParameterCarrier i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.outgoingParameterCarrier_isCompact patch i

/--
[KWAdaptivePatchedData.incomingParameterCarrier_isCompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma incomingParameterCarrier_isCompact_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  IsCompact (patch.incomingParameterCarrier i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.incomingParameterCarrier_isCompact patch i

/--
[KWAdaptivePatchedData.outgoingParameterCarrier_subset_portTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma outgoingParameterCarrier_subset_portTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.outgoingParameterCarrier i ⊆ ({polygon.vertex i + patch.beta * polygon.edgeVector i} ∪ kwTranslatedOpenRayTail (polygon.vertex i) (patch.beta * polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.outgoingParameterCarrier_subset_portTail patch i

/--
[KWAdaptivePatchedData.incomingParameterCarrier_subset_portTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma incomingParameterCarrier_subset_portTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.incomingParameterCarrier i ⊆ ({polygon.vertex (i + 1) + patch.alpha (i + 1) * (-polygon.edgeVector i)} ∪ kwTranslatedOpenRayTail (polygon.vertex (i + 1)) (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.incomingParameterCarrier_subset_portTail patch i

/--
[KWAdaptivePatchedData.firstConnector_disjoint_outgoingParameterCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma firstConnector_disjoint_outgoingParameterCarrier_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M))) (patch.outgoingParameterCarrier (i + 1)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.firstConnector_disjoint_outgoingParameterCarrier patch hcross hcoords i

/--
[KWAdaptivePatchedData.secondConnector_disjoint_incomingParameterCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma secondConnector_disjoint_incomingParameterCarrier_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  Disjoint (kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))) (patch.incomingParameterCarrier i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.secondConnector_disjoint_incomingParameterCarrier patch hcross hcoords i

/--
[KWAdaptivePatchedData.dist_middleCorner_ideal_lt_two_mul_of_interiorMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma dist_middleCorner_ideal_lt_two_mul_of_interiorMesh_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r : NNReal)
  (hfine : KWEndpointInteriorMeshWithin patch.data r) :
-- imply
  dist (patch.middleCorner i q) (patch.idealMiddleCorner i q) < 2 * r := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.dist_middleCorner_ideal_lt_two_mul_of_interiorMesh patch r hfine i q

/--
[KWAdaptivePatchedData.dist_vertex_idealVertex_lt_two_mul_of_interiorMesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma dist_vertex_idealVertex_lt_two_mul_of_interiorMesh_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r : NNReal)
  (hr : 0 < r)
  (hfine : KWEndpointInteriorMeshWithin patch.data r) :
-- imply
  ∀ j : Fin (n * (2 * (M + 1))), dist (patch.vertex j) (patch.idealVertex j) < 2 * r := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.dist_vertex_idealVertex_lt_two_mul_of_interiorMesh patch r hr hfine

/--
[KWAdaptivePatchedData.actualConnectorMiddle_disjoint_of_carrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma actualConnectorMiddle_disjoint_of_carrier_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {a : Fin (n * (2 * (M + 1)))}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
  {carrier : Set ℂ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r sep : NNReal)
  (hr : 0 < r)
  (hfine : KWEndpointInteriorMeshWithin patch.data r)
  (hcarrier : patch.idealMiddleClosedEdge i q even ⊆ carrier)
  (hsep : ∀ x ∈ kwRawClosedEdge patch.idealVertex a, ∀ y ∈ carrier, (sep : ℝ) < dist x y)
  (hsmall : 4 * (r : ℝ) < sep) :
-- imply
  Disjoint (kwRawClosedEdge patch.vertex a) (patch.middleClosedEdge i q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.actualConnectorMiddle_disjoint_of_carrier patch r sep hr hfine a i q even carrier hcarrier hsep hsmall

/--
[KWAdaptivePatchedData.exists_remoteParameter_dist_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean)
-/
@[path]
private lemma exists_remoteParameter_dist_separation_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {first : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  ∃ sep : NNReal, 0 < sep ∧ ∀ x ∈ (if first then kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1) else patch.incomingParameterCarrier i), (sep : ℝ) < dist x y := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.exists_remoteParameter_dist_separation patch hcross hcoords i first


-- created on 2026-10-23

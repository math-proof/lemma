import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveActualUniformRadius
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.exists_uniform_remoteParameter_dist_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualUniformRadius.lean)
-/
@[path]
private lemma exists_uniform_remoteParameter_dist_separation_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  ∃ sep : ℝ≥0, 0 < sep ∧ ∀ i : Fin n, ∀ first : Bool, ∀ x ∈ (if first then kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1) else patch.incomingParameterCarrier i), (sep : ℝ) < dist x y := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.exists_uniform_remoteParameter_dist_separation patch hcross hcoords

/--
[KWSmallAdaptiveConnectorScales.exists_uniform_remoteParameter_radius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualUniformRadius.lean)
-/
@[path]
private lemma exists_uniform_remoteParameter_radius_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {R : ℝ}
  {scales : KWSmallAdaptiveConnectorScales polygon R}
-- given
  (hcross : ∀ j : Fin n, kwComplexCross (polygon.edgeVector j) (polygon.edgeVector (j + 1)) ≠ 0)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0) :
-- imply
  ∃ sep : ℝ≥0, 0 < sep ∧ ∀ {M : ℕ} [NeZero M] (hM : 2 ≤ M), let patch := scales.toPatchedData hM ∀ i : Fin n, ∀ first : Bool, ∀ x ∈ (if first then kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1) else patch.incomingParameterCarrier i), (sep : ℝ) < dist x y := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.exists_uniform_remoteParameter_radius scales hcross hcoords

/--
[KWAdaptivePatchedData.firstConnector_disjoint_outgoingMiddle_of_fine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualUniformRadius.lean)
-/
@[path]
private lemma firstConnector_disjoint_outgoingMiddle_of_fine_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r sep : ℝ≥0)
  (hr : 0 < r)
  (hfine : KWEndpointInteriorMeshWithin patch.data r)
  (hsep : ∀ i : Fin n, ∀ first : Bool, ∀ x ∈ (if first then kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1) else patch.incomingParameterCarrier i), (sep : ℝ) < dist x y)
  (hsmall : 4 * (r : ℝ) < sep) :
-- imply
  Disjoint (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M))) (patch.middleClosedEdge (i + 1) q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.firstConnector_disjoint_outgoingMiddle_of_fine patch r sep hr hfine hsep hsmall i q even

/--
[KWAdaptivePatchedData.secondConnector_disjoint_incomingMiddle_of_fine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualUniformRadius.lean)
-/
@[path]
private lemma secondConnector_disjoint_incomingMiddle_of_fine_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (r sep : ℝ≥0)
  (hr : 0 < r)
  (hfine : KWEndpointInteriorMeshWithin patch.data r)
  (hsep : ∀ i : Fin n, ∀ first : Bool, ∀ x ∈ (if first then kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1) else patch.incomingParameterCarrier i), (sep : ℝ) < dist x y)
  (hsmall : 4 * (r : ℝ) < sep) :
-- imply
  Disjoint (kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))) (patch.middleClosedEdge i q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.secondConnector_disjoint_incomingMiddle_of_fine patch r sep hr hfine hsep hsmall i q even

/--
[KWAdaptivePatchedData.connector_disjoint_incomingMiddle_of_fine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualUniformRadius.lean)
-/
@[path]
private lemma connector_disjoint_incomingMiddle_of_fine_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (r sep : ℝ≥0)
  (hr : 0 < r)
  (hfine : KWEndpointInteriorMeshWithin patch.data r)
  (hsep : ∀ i : Fin n, ∀ first : Bool, ∀ x ∈ (if first then kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1) else patch.incomingParameterCarrier i), (sep : ℝ) < dist x y)
  (hsmall : 4 * (r : ℝ) < sep)
  (hnotLast : q ≠ patch.lastMiddleIndex ∨ even = true) :
-- imply
  Disjoint (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) ∪ kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))) (patch.middleClosedEdge i q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_disjoint_incomingMiddle_of_fine patch hcoords r sep hr hfine hsep hsmall i q even hnotLast

/--
[KWAdaptivePatchedData.connector_disjoint_outgoingMiddle_of_fine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualUniformRadius.lean)
-/
@[path]
private lemma connector_disjoint_outgoingMiddle_of_fine_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hcoords : ∀ j : Fin n, (polygon.edgeVector j).re ≠ 0 ∧ (polygon.edgeVector j).im ≠ 0)
  (r sep : ℝ≥0)
  (hr : 0 < r)
  (hfine : KWEndpointInteriorMeshWithin patch.data r)
  (hsep : ∀ i : Fin n, ∀ first : Bool, ∀ x ∈ (if first then kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i (Fin.last M)) else kwRawClosedEdge patch.idealVertex (kwStairOddIndex i (Fin.last M))), ∀ y ∈ (if first then patch.outgoingParameterCarrier (i + 1) else patch.incomingParameterCarrier i), (sep : ℝ) < dist x y)
  (hsmall : 4 * (r : ℝ) < sep)
  (hnotFirst : q ≠ 0 ∨ even = false) :
-- imply
  Disjoint (kwRawClosedEdge patch.vertex (kwStairEvenIndex i (Fin.last M)) ∪ kwRawClosedEdge patch.vertex (kwStairOddIndex i (Fin.last M))) (patch.middleClosedEdge (i + 1) q even) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.connector_disjoint_outgoingMiddle_of_fine patch hcoords r sep hr hfine hsep hsmall i q even hnotFirst

/--
[KWSmallAdaptiveConnectorScales.exists_interiorMesh_patch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualUniformRadius.lean)
-/
@[path]
private lemma exists_interiorMesh_patch_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {R : ℝ}
  {scales : KWSmallAdaptiveConnectorScales polygon R}
-- given
  (r : ℝ≥0)
  (hr : 0 < r) :
-- imply
  ∃ M : ℕ, ∃ hM : 2 ≤ M, letI : NeZero M := ⟨by omega⟩ KWEndpointInteriorMeshWithin (scales.toPatchedData hM).data r := by
-- proof
  apply StatMech.FrontierA.KWSmallAdaptiveConnectorScales.exists_interiorMesh_patch scales r hr


-- created on 2026-10-23

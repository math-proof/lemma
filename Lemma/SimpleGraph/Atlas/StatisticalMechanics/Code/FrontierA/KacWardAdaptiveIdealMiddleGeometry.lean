import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealMiddleGeometry
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.idealMiddleCorner_eq_lineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealMiddleGeometry.lean)
-/
@[path]
private lemma idealMiddleCorner_eq_lineMap_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.idealMiddleCorner i q = AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) ((patch.data.parameter i q.succ.castSucc.castSucc + patch.data.parameter i q.succ.castSucc.succ) / 2) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleCorner_eq_lineMap patch i q

/--
[KWAdaptivePatchedData.idealMiddleClosedEdge_point_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealMiddleGeometry.lean)
-/
@[path]
private lemma idealMiddleClosedEdge_point_parameter_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
  {z : ℂ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hz : z ∈ patch.idealMiddleClosedEdge i q even) :
-- imply
  ∃ u ∈ Icc (patch.data.parameter i q.succ.castSucc.castSucc) (patch.data.parameter i q.succ.castSucc.succ), z = AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) u := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleClosedEdge_point_parameter patch i q even hz

/--
[KWAdaptivePatchedData.idealMiddleClosedEdge_point_halfParameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealMiddleGeometry.lean)
-/
@[path]
private lemma idealMiddleClosedEdge_point_halfParameter_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
  {z : ℂ}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hz : z ∈ patch.idealMiddleClosedEdge i q even) :
-- imply
  ∃ u ∈ if even then Icc (patch.data.parameter i q.succ.castSucc.castSucc) ((patch.data.parameter i q.succ.castSucc.castSucc + patch.data.parameter i q.succ.castSucc.succ) / 2) else Icc ((patch.data.parameter i q.succ.castSucc.castSucc + patch.data.parameter i q.succ.castSucc.succ) / 2) (patch.data.parameter i q.succ.castSucc.succ), z = AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) u := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleClosedEdge_point_halfParameter patch i q even hz

/--
[KWAdaptivePatchedData.idealMiddleClosedEdge_subset_outgoingPortRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealMiddleGeometry.lean)
-/
@[path]
private lemma idealMiddleClosedEdge_subset_outgoingPortRay_eq
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
  patch.idealMiddleClosedEdge i q even ⊆ (fun w : ℂ ↦ polygon.vertex i + w) '' ({patch.beta * polygon.edgeVector i} ∪ kwOpenRayTail (patch.beta * polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleClosedEdge_subset_outgoingPortRay patch i q even

/--
[KWAdaptivePatchedData.idealMiddleClosedEdge_subset_incomingPortRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealMiddleGeometry.lean)
-/
@[path]
private lemma idealMiddleClosedEdge_subset_incomingPortRay_eq
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
  patch.idealMiddleClosedEdge i q even ⊆ (fun w : ℂ ↦ polygon.vertex (i + 1) + w) '' ({patch.alpha (i + 1) * (-polygon.edgeVector i)} ∪ kwOpenRayTail (patch.alpha (i + 1) * (-polygon.edgeVector i))) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleClosedEdge_subset_incomingPortRay patch i q even

/--
[KWAdaptivePatchedData.idealMiddleClosedEdge_subset_outgoingRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealMiddleGeometry.lean)
-/
@[path]
private lemma idealMiddleClosedEdge_subset_outgoingRay_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hnotFirst : q ≠ 0 ∨ even = false) :
-- imply
  patch.idealMiddleClosedEdge i q even ⊆ (fun w : ℂ ↦ polygon.vertex i + w) '' kwOpenRayTail (patch.beta * polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleClosedEdge_subset_outgoingRay patch i q even hnotFirst

/--
[KWAdaptivePatchedData.idealMiddleClosedEdge_subset_incomingRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealMiddleGeometry.lean)
-/
@[path]
private lemma idealMiddleClosedEdge_subset_incomingRay_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
  {even : Bool}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hnotLast : q ≠ patch.lastMiddleIndex ∨ even = true) :
-- imply
  patch.idealMiddleClosedEdge i q even ⊆ (fun w : ℂ ↦ polygon.vertex (i + 1) + w) '' kwOpenRayTail (patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealMiddleClosedEdge_subset_incomingRay patch i q even hnotLast


-- created on 2026-10-23

import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealIncidentRays
open StatMech StatMech.FrontierA


/--
[KWAdaptivePatchedData.beta_le_retainedParameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma beta_le_retainedParameter_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.beta ≤ patch.data.parameter i q.succ.castSucc.castSucc := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.beta_le_retainedParameter patch i q

/--
[KWAdaptivePatchedData.beta_lt_retainedParameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma beta_lt_retainedParameter_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hq : q ≠ 0) :
-- imply
  patch.beta < patch.data.parameter i q.succ.castSucc.castSucc := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.beta_lt_retainedParameter patch i q hq

/--
[KWAdaptivePatchedData.retainedNextParameter_le_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma retainedNextParameter_le_incoming_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  patch.data.parameter i q.succ.castSucc.succ ≤ 1 - patch.alpha (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.retainedNextParameter_le_incoming patch i q

/--
[KWAdaptivePatchedData.retainedNextParameter_lt_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma retainedNextParameter_lt_incoming_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hq : q ≠ patch.lastMiddleIndex) :
-- imply
  patch.data.parameter i q.succ.castSucc.succ < 1 - patch.alpha (i + 1) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.retainedNextParameter_lt_incoming patch i q hq

/--
[KWAdaptivePatchedData.idealRawClosedEdge_even_subset_outgoingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma idealRawClosedEdge_even_subset_outgoingTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hq : q ≠ 0) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) ⊆ kwTranslatedOpenRayTail (polygon.vertex i) (patch.beta * polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_even_subset_outgoingTail patch i q hq

/--
[KWAdaptivePatchedData.idealRawClosedEdge_even_subset_outgoingPortTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma idealRawClosedEdge_even_subset_outgoingPortTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) ⊆ {polygon.vertex i + patch.beta * polygon.edgeVector i} ∪ kwTranslatedOpenRayTail (polygon.vertex i) (patch.beta * polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_even_subset_outgoingPortTail patch i q

/--
[KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_outgoingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma idealRawClosedEdge_odd_subset_outgoingTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) ⊆ kwTranslatedOpenRayTail (polygon.vertex i) (patch.beta * polygon.edgeVector i) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_outgoingTail patch i q

/--
[KWAdaptivePatchedData.idealRawClosedEdge_even_subset_incomingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma idealRawClosedEdge_even_subset_incomingTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairEvenIndex i q.castSucc) ⊆ kwTranslatedOpenRayTail (polygon.vertex (i + 1)) (patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_even_subset_incomingTail patch i q

/--
[KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_incomingTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma idealRawClosedEdge_odd_subset_incomingTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon)
  (hq : q ≠ patch.lastMiddleIndex) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) ⊆ kwTranslatedOpenRayTail (polygon.vertex (i + 1)) (patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_incomingTail patch i q hq

/--
[KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_incomingPortTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealIncidentRays.lean)
-/
@[path]
private lemma idealRawClosedEdge_odd_subset_incomingPortTail_eq
  {n M : ℕ}
  [NeZero n]
  [NeZero M]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {q : Fin M}
-- given
  (patch : KWAdaptivePatchedData (M := M) polygon) :
-- imply
  kwRawClosedEdge patch.idealVertex (kwStairOddIndex i q.castSucc) ⊆ {polygon.vertex (i + 1) + patch.alpha (i + 1) * (-polygon.edgeVector i)} ∪ kwTranslatedOpenRayTail (polygon.vertex (i + 1)) (patch.alpha (i + 1) * (-polygon.edgeVector i)) := by
-- proof
  apply StatMech.FrontierA.KWAdaptivePatchedData.idealRawClosedEdge_odd_subset_incomingPortTail patch i q


-- created on 2026-10-23

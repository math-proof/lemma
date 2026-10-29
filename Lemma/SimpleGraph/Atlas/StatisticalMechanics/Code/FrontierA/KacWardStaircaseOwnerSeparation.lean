import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStaircaseOwnerSeparation
open StatMech StatMech.FrontierA


/--
[kwStairOwner_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseOwnerSeparation.lean)
-/
@[path]
private lemma kwStairOwner_even_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {i : Fin n}
  {k : Fin S} :
-- imply
  kwStairOwner (kwStairEvenIndex i k) = i := by
-- proof
  apply StatMech.FrontierA.kwStairOwner_even i k

/--
[kwStairOwner_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseOwnerSeparation.lean)
-/
@[path]
private lemma kwStairOwner_odd_eq
  {n S : ℕ}
  [NeZero n]
  [NeZero S]
  {i : Fin n}
  {k : Fin S} :
-- imply
  kwStairOwner (kwStairOddIndex i k) = i := by
-- proof
  apply StatMech.FrontierA.kwStairOwner_odd i k

/--
[KWStairParameterData.rawClosedEdge_subset_ownerTube_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseOwnerSeparation.lean)
-/
@[path]
private lemma rawClosedEdge_subset_ownerTube_exact_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j : Fin (n * (2 * (M + 1)))}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (r : NNReal)
  (hr : 0 < r)
  (hfine : data.MeshWithin r) :
-- imply
  kwRawClosedEdge data.vertex j ⊆ polygon.closedEdgeTube r (kwStairOwner j) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdge_subset_ownerTube_exact data r hr hfine j

/--
[KWStairParameterData.rawClosedEdges_disjoint_of_owner_nonincident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseOwnerSeparation.lean)
-/
@[path]
private lemma rawClosedEdges_disjoint_of_owner_nonincident_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j l : Fin (n * (2 * (M + 1)))}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (r : NNReal)
  (hr : 0 < r)
  (hfine : data.MeshWithin r)
  (htubes : ∀ i j : Fin n, KWEdgesNonincident i j → Disjoint (polygon.closedEdgeTube r i) (polygon.closedEdgeTube r j))
  (howners : KWEdgesNonincident (kwStairOwner j) (kwStairOwner l)) :
-- imply
  Disjoint (kwRawClosedEdge data.vertex j) (kwRawClosedEdge data.vertex l) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdges_disjoint_of_owner_nonincident data r hr hfine htubes j l howners

/--
[KWStairParameterData.rawClosedEdges_disjoint_of_sameOwner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseOwnerSeparation.lean)
-/
@[path]
private lemma rawClosedEdges_disjoint_of_sameOwner_eq
  {n M : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {j l : Fin (n * (2 * (M + 1)))}
-- given
  (data : KWStairParameterData (S := M + 1) polygon)
  (hcoords : ∀ i : Fin n, (polygon.edgeVector i).re ≠ 0 ∧ (polygon.edgeVector i).im ≠ 0)
  (howner : kwStairOwner j = kwStairOwner l)
  (hnon : KWEdgesNonincident j l) :
-- imply
  Disjoint (kwRawClosedEdge data.vertex j) (kwRawClosedEdge data.vertex l) := by
-- proof
  apply StatMech.FrontierA.KWStairParameterData.rawClosedEdges_disjoint_of_sameOwner data hcoords j l howner hnon


-- created on 2026-10-23

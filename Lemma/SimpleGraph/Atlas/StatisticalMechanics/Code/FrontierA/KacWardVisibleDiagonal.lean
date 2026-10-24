import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardVisibleDiagonal
open StatMech StatMech.FrontierA


/--
[kwTriangleBaseHeight_lineMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma kwTriangleBaseHeight_lineMap_eq
  {A C X Y : ℂ}
  {t : ℝ} :
-- imply
  kwTriangleBaseHeight A C (AffineMap.lineMap X Y t) = (1 - t) * kwTriangleBaseHeight A C X + t * kwTriangleBaseHeight A C Y := by
-- proof
  apply StatMech.FrontierA.kwTriangleBaseHeight_lineMap A C X Y t

/--
[kwTriangleBaseHeight_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma kwTriangleBaseHeight_sub_eq
  {A B C P : ℂ} :
-- imply
  kwTriangleBaseHeight A C B - kwTriangleBaseHeight A C P = kwComplexCross (A - B) (P - B) - kwComplexCross (C - B) (P - B) := by
-- proof
  apply StatMech.FrontierA.kwTriangleBaseHeight_sub A B C P

/--
[kwTriangleBaseHeight_lt_apex_of_wedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma kwTriangleBaseHeight_lt_apex_of_wedge_eq
  {A B C P : ℂ}
-- given
  (hAC : 0 < kwComplexCross (A - B) (C - B))
  (hAP : 0 ≤ kwComplexCross (A - B) (P - B))
  (hCP : kwComplexCross (C - B) (P - B) ≤ 0)
  (hPB : P ≠ B) :
-- imply
  kwTriangleBaseHeight A C P < kwTriangleBaseHeight A C B := by
-- proof
  apply StatMech.FrontierA.kwTriangleBaseHeight_lt_apex_of_wedge hAC hAP hCP hPB

/--
[kw_openSegments_disjoint_of_common_left_no_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma kw_openSegments_disjoint_of_common_left_no_between_eq
  {B P Q : ℂ}
-- given
  (hBP : B ≠ P)
  (hBQ : B ≠ Q)
  (hPQ : P ≠ Q)
  (hQnot : ¬Sbtw ℝ B Q P)
  (hPnot : ¬Sbtw ℝ B P Q) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ B z P} {z : ℂ | Sbtw ℝ B z Q} := by
-- proof
  apply StatMech.FrontierA.kw_openSegments_disjoint_of_common_left_no_between hBP hBQ hPQ hQnot hPnot

/--
[KWFiniteSimplePolygon.chordIsClean_of_heightBarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma chordIsClean_of_heightBarrier_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i j : Fin n}
  {A C : ℂ}
-- given
  (hij : i ≠ j)
  (hforward : j ≠ i + 1)
  (hbackward : i ≠ j + 1)
  (hhigh : kwTriangleBaseHeight A C (polygon.vertex j) < kwTriangleBaseHeight A C (polygon.vertex i))
  (hmax : ∀ k : Fin n, k ≠ i → kwTriangleBaseHeight A C (polygon.vertex k) ≤ kwTriangleBaseHeight A C (polygon.vertex j)) :
-- imply
  polygon.ChordIsClean i j := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.chordIsClean_of_heightBarrier polygon i j hij hforward hbackward A C hhigh hmax

/--
[KWFiniteSimplePolygon.exists_maxHeightVertex_of_wedge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma exists_maxHeightVertex_of_wedge_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {A C : ℂ}
-- given
  (hAC : 0 < kwComplexCross (A - polygon.vertex i) (C - polygon.vertex i))
  (hwedge : ∀ k : Fin n, k ≠ i → 0 ≤ kwComplexCross (A - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ∧ kwComplexCross (C - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ≤ 0) :
-- imply
  ∃ j : Fin n, j ≠ i ∧ kwTriangleBaseHeight A C (polygon.vertex j) < kwTriangleBaseHeight A C (polygon.vertex i) ∧ ∀ k : Fin n, k ≠ i → kwTriangleBaseHeight A C (polygon.vertex k) ≤ kwTriangleBaseHeight A C (polygon.vertex j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_maxHeightVertex_of_wedge polygon i A C hAC hwedge

/--
[KWFiniteSimplePolygon.exists_heightBarrierChord_or_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma exists_heightBarrierChord_or_neighbor_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
  {A C : ℂ}
-- given
  (hAC : 0 < kwComplexCross (A - polygon.vertex i) (C - polygon.vertex i))
  (hwedge : ∀ k : Fin n, k ≠ i → 0 ≤ kwComplexCross (A - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ∧ kwComplexCross (C - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ≤ 0) :
-- imply
  ∃ j : Fin n, j ≠ i ∧ (j = i + 1 ∨ i = j + 1 ∨ polygon.ChordIsClean i j) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_heightBarrierChord_or_neighbor polygon i A C hAC hwedge

/--
[KWFiniteSimplePolygon.tangentWedge_cross_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma tangentWedge_cross_pos_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i lower upper : Fin n}
-- given
  (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ))
  (hlowerI : lower ≠ i)
  (hupperI : upper ≠ i)
  (hsupport : ∀ j : Fin n, j ≠ i → kwComplexDot (polygon.vertex i) (polygon.vertex j - polygon.vertex i) < 0)
  (hlowerSide : ∀ k : Fin n, kwComplexCross (polygon.vertex lower - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ≤ 0)
  (hupperSide : ∀ k : Fin n, 0 ≤ kwComplexCross (polygon.vertex upper - polygon.vertex i) (polygon.vertex k - polygon.vertex i)) :
-- imply
  0 < kwComplexCross (polygon.vertex upper - polygon.vertex i) (polygon.vertex lower - polygon.vertex i) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.tangentWedge_cross_pos polygon hnoncollinear i lower upper hlowerI hupperI hsupport hlowerSide hupperSide

/--
[KWFiniteSimplePolygon.exists_visibleChord_or_strictNeighborSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma exists_visibleChord_or_strictNeighborSeparation_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i a c : Fin n}
-- given
  (hac : a ≠ c)
  (haNeighbor : a = i + 1 ∨ i = a + 1)
  (hcNeighbor : c = i + 1 ∨ i = c + 1)
  (hAC : 0 < kwComplexCross (polygon.vertex a - polygon.vertex i) (polygon.vertex c - polygon.vertex i))
  (hwedge : ∀ k : Fin n, k ≠ i → 0 ≤ kwComplexCross (polygon.vertex a - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ∧ kwComplexCross (polygon.vertex c - polygon.vertex i) (polygon.vertex k - polygon.vertex i) ≤ 0) :
-- imply
  (∃ j : Fin n, j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧ polygon.ChordIsClean i j) ∨ (0 < kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c) (polygon.vertex i) ∧ ∀ k : Fin n, k ≠ i → k ≠ a → k ≠ c → kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c) (polygon.vertex k) < 0) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_visibleChord_or_strictNeighborSeparation polygon i a c hac haNeighbor hcNeighbor hAC hwedge

/--
[KWFiniteSimplePolygon.exists_visibleChord_or_strictNeighborSeparation_global](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma exists_visibleChord_or_strictNeighborSeparation_global_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  (∃ i j : Fin n, i ≠ j ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧ polygon.ChordIsClean i j) ∨ (∃ i a c : Fin n, a ≠ c ∧ (a = i + 1 ∨ i = a + 1) ∧ (c = i + 1 ∨ i = c + 1) ∧ 0 < kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c) (polygon.vertex i) ∧ ∀ k : Fin n, k ≠ i → k ≠ a → k ≠ c → kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c) (polygon.vertex k) < 0) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_visibleChord_or_strictNeighborSeparation_global polygon hnoncollinear

/--
[KWFiniteSimplePolygon.exists_rotated_vertexOneStrictlySeparated_of_neighborSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma exists_rotated_vertexOneStrictlySeparated_of_neighborSeparation_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
  {i a c : Fin (m + 3)}
-- given
  (hac : a ≠ c)
  (haNeighbor : a = i + 1 ∨ i = a + 1)
  (hcNeighbor : c = i + 1 ∨ i = c + 1)
  (hApex : 0 < kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c) (polygon.vertex i))
  (hrest : ∀ k : Fin (m + 3), k ≠ i → k ≠ a → k ≠ c → kwTriangleBaseHeight (polygon.vertex a) (polygon.vertex c) (polygon.vertex k) < 0) :
-- imply
  ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneStrictlySeparated := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_rotated_vertexOneStrictlySeparated_of_neighborSeparation polygon i a c hac haNeighbor hcNeighbor hApex hrest

/--
[KWFiniteSimplePolygon.exists_visibleChord_or_rotated_strictlySeparated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardVisibleDiagonal.lean)
-/
@[path]
private lemma exists_visibleChord_or_rotated_strictlySeparated_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  (∃ i j : Fin (m + 3), i ≠ j ∧ j ≠ i + 1 ∧ i ≠ j + 1 ∧ polygon.ChordIsClean i j) ∨ (∃ r : Fin (m + 3), (polygon.rotate r).VertexOneStrictlySeparated) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_visibleChord_or_rotated_strictlySeparated polygon hnoncollinear


-- created on 2026-10-23

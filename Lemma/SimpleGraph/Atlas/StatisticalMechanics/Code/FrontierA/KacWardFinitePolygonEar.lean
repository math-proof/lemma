import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar
open StatMech StatMech.FrontierA


/--
[kw_sbtw_iff_mem_openSegment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kw_sbtw_iff_mem_openSegment_eq
  {x y z : ℂ}
-- given
  (hxz : x ≠ z) :
-- imply
  Sbtw ℝ x y z ↔ y ∈ openSegment ℝ x z := by
-- proof
  apply StatMech.FrontierA.kw_sbtw_iff_mem_openSegment hxz

/--
[kw_sbtw_eq_or_sbtw_or_sbtw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kw_sbtw_eq_or_sbtw_or_sbtw_eq
  {a b c z : ℂ}
-- given
  (hac : a ≠ c)
  (hab : a ≠ b)
  (hbc : b ≠ c)
  (hbetween : Wbtw ℝ a b c)
  (hz : Sbtw ℝ a z c) :
-- imply
  z = b ∨ Sbtw ℝ a z b ∨ Sbtw ℝ b z c := by
-- proof
  apply StatMech.FrontierA.kw_sbtw_eq_or_sbtw_or_sbtw hac hab hbc hbetween hz

/--
[kwComplexCross_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwComplexCross_add_right_eq
  {a b c : ℂ} :
-- imply
  kwComplexCross a (b + c) = kwComplexCross a b + kwComplexCross a c := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_add_right a b c

/--
[kwComplexCross_sub_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwComplexCross_sub_right_eq
  {a b c : ℂ} :
-- imply
  kwComplexCross a (b - c) = kwComplexCross a b - kwComplexCross a c := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_sub_right a b c

/--
[kwComplexCross_mul_real_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwComplexCross_mul_real_left_eq
  {r : ℝ}
  {a b : ℂ} :
-- imply
  kwComplexCross ((r : ℂ) * a) b = r * kwComplexCross a b := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_mul_real_left r a b

/--
[kwComplexCross_mul_real_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwComplexCross_mul_real_right_eq
  {r : ℝ}
  {a b : ℂ} :
-- imply
  kwComplexCross a ((r : ℂ) * b) = r * kwComplexCross a b := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_mul_real_right r a b

/--
[kwComplexCross_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwComplexCross_self_eq
  {a : ℂ} :
-- imply
  kwComplexCross a a = 0 := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_self a

/--
[kwComplexCross_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwComplexCross_swap_eq
  {a b : ℂ} :
-- imply
  kwComplexCross a b = -kwComplexCross b a := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_swap a b

/--
[kwComplexCross_neg_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwComplexCross_neg_right_eq
  {a b : ℂ} :
-- imply
  kwComplexCross a (-b) = -kwComplexCross a b := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_neg_right a b

/--
[kw_exists_common_sbtw_of_cross_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kw_exists_common_sbtw_of_cross_opposite_eq
  {A B C D : ℂ}
-- given
  (hAB : kwComplexCross (B - A) (C - A) * kwComplexCross (B - A) (D - A) < 0)
  (hCD : kwComplexCross (D - C) (A - C) * kwComplexCross (D - C) (B - C) < 0) :
-- imply
  ∃ z : ℂ, Sbtw ℝ A z B ∧ Sbtw ℝ C z D := by
-- proof
  apply StatMech.FrontierA.kw_exists_common_sbtw_of_cross_opposite hAB hCD

/--
[kwComplexCross_eq_zero_of_sbtw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwComplexCross_eq_zero_of_sbtw_eq
  {A B C : ℂ}
-- given
  (h : Sbtw ℝ A B C) :
-- imply
  kwComplexCross (C - A) (B - A) = 0 := by
-- proof
  apply StatMech.FrontierA.kwComplexCross_eq_zero_of_sbtw h

/--
[kw_openSegments_disjoint_of_common_left_cross_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kw_openSegments_disjoint_of_common_left_cross_ne_eq
  {A B C : ℂ}
-- given
  (hcross : kwComplexCross (B - A) (C - A) ≠ 0) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ A z B} {z : ℂ | Sbtw ℝ A z C} := by
-- proof
  apply StatMech.FrontierA.kw_openSegments_disjoint_of_common_left_cross_ne hcross

/--
[kw_fourVector_crossEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kw_fourVector_crossEar_eq
  {p a b q : ℂ}
-- given
  (hb : b ≠ 0)
  (hq : q ≠ 0)
  (hsum : p + a + b + q = 0)
  (hbq : kwComplexCross b q ≠ 0)
  (hsign : (0 < kwComplexCross p a ∧ 0 < kwComplexCross a b ∧ 0 < kwComplexCross q p) ∨ (kwComplexCross p a < 0 ∧ kwComplexCross a b < 0 ∧ kwComplexCross q p < 0)) :
-- imply
  kwComplexCross a b ≠ 0 ∧ (Complex.arg q : Real.Angle) - (Complex.arg b : Real.Angle) ≠ (Real.pi : Real.Angle) ∧ ((0 < kwComplexCross p a ∧ 0 < kwComplexCross p (a + b)) ∨ (kwComplexCross p a < 0 ∧ kwComplexCross p (a + b) < 0)) ∧ ((0 < kwComplexCross (a + b) b ∧ 0 < kwComplexCross (a + b) q) ∨ (kwComplexCross (a + b) b < 0 ∧ kwComplexCross (a + b) q < 0)) := by
-- proof
  apply StatMech.FrontierA.kw_fourVector_crossEar p a b q hb hq hsum hbq hsign

/--
[kwVectorTurnPhase_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorTurnPhase_ne_zero_eq
  {x y : ℂ} :
-- imply
  kwVectorTurnPhase x y ≠ 0 := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_ne_zero x y

/--
[kwVectorPhasePath_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhasePath_nil_eq :
-- imply
  kwVectorPhasePath [] = 1 := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_nil

/--
[kwVectorPhasePath_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhasePath_singleton_eq
  {x : ℂ} :
-- imply
  kwVectorPhasePath [x] = 1 := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_singleton x

/--
[kwVectorPhasePath_cons_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhasePath_cons_cons_eq
  {x y : ℂ}
  {tail : List ℂ} :
-- imply
  kwVectorPhasePath (x :: y :: tail) = kwVectorTurnPhase x y * kwVectorPhasePath (y :: tail) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_cons_cons x y tail

/--
[kwVectorPhaseCycle_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_nil_eq :
-- imply
  kwVectorPhaseCycle [] = 1 := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_nil

/--
[kwVectorPhaseCycle_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_cons_eq
  {x : ℂ}
  {tail : List ℂ} :
-- imply
  kwVectorPhaseCycle (x :: tail) = kwVectorPhasePath (x :: tail) * kwVectorTurnPhase ((x :: tail).getLastD x) x := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_cons x tail

/--
[kwVectorPhasePath_mul_last_eq_zipWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhasePath_mul_last_eq_zipWith_eq
  {x closing : ℂ}
  {tail : List ℂ} :
-- imply
  kwVectorPhasePath (x :: tail) * kwVectorTurnPhase ((x :: tail).getLastD x) closing = (List.zipWith kwVectorTurnPhase (x :: tail) (tail ++ [closing])).prod := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_mul_last_eq_zipWith x closing tail

/--
[kwVectorPhaseCycle_eq_zipWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_eq_zipWith_eq
  {edges : List ℂ} :
-- imply
  kwVectorPhaseCycle edges = (List.zipWith kwVectorTurnPhase edges (edges.rotate 1)).prod := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_eq_zipWith edges

/--
[kwVectorPhaseCycle_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_rotate_eq
  {edges : List ℂ}
  {r : ℕ} :
-- imply
  kwVectorPhaseCycle (edges.rotate r) = kwVectorPhaseCycle edges := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_rotate edges r

/--
[kwVectorPhaseCycle_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_ofFn_eq
  {n : ℕ}
  [NeZero n]
  {edge : Fin n → ℂ} :
-- imply
  kwVectorPhaseCycle (List.ofFn edge) = kwLoopPhaseProduct kwVectorTurnPhase edge := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_ofFn edge

/--
[KWStraightLineEmbedding.vectorTurnPhase_eq_turnPhase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vectorTurnPhase_eq_turnPhase_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {dart next : G.Dart} :
-- imply
  kwVectorTurnPhase (embedding.vertex dart.snd - embedding.vertex dart.fst) (embedding.vertex next.snd - embedding.vertex next.fst) = embedding.turnPhase dart next := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.vectorTurnPhase_eq_turnPhase embedding dart next

/--
[KWStraightLineEmbedding.vectorPhaseCycle_of_dartLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vectorPhaseCycle_of_dartLoop_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {n : ℕ}
  [NeZero n]
  {loop : Fin n → G.Dart} :
-- imply
  kwVectorPhaseCycle (List.ofFn fun k ↦ embedding.vertex (loop k).snd - embedding.vertex (loop k).fst) = kwLoopPhaseProduct embedding.turnPhase loop := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.vectorPhaseCycle_of_dartLoop embedding loop

/--
[KWStraightLineEmbedding.incident_collinear_sameRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma incident_collinear_sameRay_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {dart next : G.Dart}
-- given
  (hadj : dart.snd = next.fst)
  (houter : dart.fst ≠ next.snd)
  (hcol : Collinear ℝ ({embedding.vertex dart.fst, embedding.vertex dart.snd, embedding.vertex next.snd} : Set ℂ)) :
-- imply
  SameRay ℝ (embedding.vertex dart.snd - embedding.vertex dart.fst) (embedding.vertex next.snd - embedding.vertex next.fst) := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.incident_collinear_sameRay embedding dart next hadj houter hcol

/--
[kwRemoveVertexOne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwRemoveVertexOne_zero_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin (n + 1) → ℂ} :
-- imply
  kwRemoveVertexOne vertex 0 = vertex 0 := by
-- proof
  apply StatMech.FrontierA.kwRemoveVertexOne_zero vertex

/--
[kwRemoveVertexOne_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwRemoveVertexOne_one_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin (n + 1) → ℂ}
-- given
  (hn : 2 ≤ n) :
-- imply
  kwRemoveVertexOne vertex 1 = vertex 2 := by
-- proof
  apply StatMech.FrontierA.kwRemoveVertexOne_one hn vertex

/--
[kwRemoveVertexOne_succ_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwRemoveVertexOne_succ_fixed_eq
  {m : ℕ}
  {vertex : Fin (m + 3) → ℂ}
  {i : Fin (m + 1)} :
-- imply
  kwRemoveVertexOne vertex i.succ = vertex i.succ.succ := by
-- proof
  apply StatMech.FrontierA.kwRemoveVertexOne_succ_fixed vertex i

/--
[kwCyclicEdgeVector_removeVertexOne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwCyclicEdgeVector_removeVertexOne_zero_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin (n + 1) → ℂ}
-- given
  (hn : 2 ≤ n) :
-- imply
  kwCyclicEdgeVector (kwRemoveVertexOne vertex) 0 = kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1 := by
-- proof
  apply StatMech.FrontierA.kwCyclicEdgeVector_removeVertexOne_zero hn vertex

/--
[kwCyclicEdgeVector_removeVertexOne_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwCyclicEdgeVector_removeVertexOne_succ_eq
  {m : ℕ}
  {vertex : Fin (m + 3) → ℂ}
  {i : Fin (m + 1)} :
-- imply
  kwCyclicEdgeVector (kwRemoveVertexOne vertex) i.succ = kwCyclicEdgeVector vertex i.succ.succ := by
-- proof
  apply StatMech.FrontierA.kwCyclicEdgeVector_removeVertexOne_succ vertex i

/--
[kwRemoveVertexOne_succ_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwRemoveVertexOne_succ_add_one_eq
  {m : ℕ}
  {vertex : Fin (m + 3) → ℂ}
  {i : Fin (m + 1)} :
-- imply
  kwRemoveVertexOne vertex (i.succ + 1) = vertex (i.succ.succ + 1) := by
-- proof
  apply StatMech.FrontierA.kwRemoveVertexOne_succ_add_one vertex i

/--
[kwCyclicEdgeList_removeVertexOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwCyclicEdgeList_removeVertexOne_eq
  {m : ℕ}
  {vertex : Fin (m + 3) → ℂ} :
-- imply
  kwCyclicEdgeList (kwRemoveVertexOne vertex) = (kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1) :: List.ofFn (fun i : Fin (m + 1) ↦ kwCyclicEdgeVector vertex i.succ.succ) := by
-- proof
  apply StatMech.FrontierA.kwCyclicEdgeList_removeVertexOne vertex

/--
[kwCyclicEdgeList_eq_first_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwCyclicEdgeList_eq_first_two_eq
  {m : ℕ}
  {vertex : Fin (m + 3) → ℂ} :
-- imply
  kwCyclicEdgeList vertex = kwCyclicEdgeVector vertex 0 :: kwCyclicEdgeVector vertex 1 :: List.ofFn (fun i : Fin (m + 1) ↦ kwCyclicEdgeVector vertex i.succ.succ) := by
-- proof
  apply StatMech.FrontierA.kwCyclicEdgeList_eq_first_two vertex

/--
[KWFiniteSimplePolygon.edgeVector_eq_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma edgeVector_eq_cyclic_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n} :
-- imply
  polygon.edgeVector i = kwCyclicEdgeVector polygon.vertex i := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.edgeVector_eq_cyclic polygon i

/--
[KWFiniteSimplePolygon.edgeList_eq_cyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma edgeList_eq_cyclic_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n} :
-- imply
  polygon.edgeList = kwCyclicEdgeList polygon.vertex := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.edgeList_eq_cyclic polygon

/--
[KWFiniteSimplePolygon.rotate_edgeVector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma rotate_edgeVector_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {r i : Fin n} :
-- imply
  (polygon.rotate r).edgeVector i = polygon.edgeVector (i + r) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.rotate_edgeVector polygon r i

/--
[KWFiniteSimplePolygon.rotate_not_collinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma rotate_not_collinear_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {r : Fin n}
-- given
  (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  ∀ i : Fin n, ¬Collinear ℝ ({(polygon.rotate r).vertex i, (polygon.rotate r).vertex (i + 1), (polygon.rotate r).vertex (i + 2)} : Set ℂ) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.rotate_not_collinear polygon hnoncollinear r

/--
[KWFiniteSimplePolygon.rotate_edgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma rotate_edgeList_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {r : Fin n} :
-- imply
  (polygon.rotate r).edgeList = polygon.edgeList.rotate r.val := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.rotate_edgeList polygon r

/--
[KWFiniteSimplePolygon.edgeVector_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma edgeVector_ne_zero_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n} :
-- imply
  polygon.edgeVector i ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.edgeVector_ne_zero polygon i

/--
[KWFiniteSimplePolygon.quadrilateral_edge_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma quadrilateral_edge_sum_eq
  {polygon : KWFiniteSimplePolygon 4}
  {i : Fin 4} :
-- imply
  polygon.edgeVector i + polygon.edgeVector (i + 1) + polygon.edgeVector (i + 2) + polygon.edgeVector (i + 3) = 0 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.quadrilateral_edge_sum polygon i

/--
[KWFiniteSimplePolygon.edge_cross_ne_zero_of_not_collinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma edge_cross_ne_zero_of_not_collinear_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hnoncollinear : ∀ i : Fin n, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ≠ 0 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.edge_cross_ne_zero_of_not_collinear polygon hnoncollinear i

/--
[KWFiniteSimplePolygon.quadrilateral_not_cross_pattern_zero_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma quadrilateral_not_cross_pattern_zero_two_eq
  {polygon : KWFiniteSimplePolygon 4} :
-- imply
  ¬(kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) * kwComplexCross (polygon.edgeVector 3) (polygon.edgeVector 0) < 0 ∧ kwComplexCross (polygon.edgeVector 1) (polygon.edgeVector 2) * kwComplexCross (polygon.edgeVector 2) (polygon.edgeVector 3) < 0) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.quadrilateral_not_cross_pattern_zero_two polygon

/--
[KWFiniteSimplePolygon.quadrilateral_not_cross_pattern_one_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma quadrilateral_not_cross_pattern_one_three_eq
  {polygon : KWFiniteSimplePolygon 4} :
-- imply
  ¬(kwComplexCross (polygon.edgeVector 1) (polygon.edgeVector 2) * kwComplexCross (polygon.edgeVector 0) (polygon.edgeVector 1) < 0 ∧ kwComplexCross (polygon.edgeVector 2) (polygon.edgeVector 3) * kwComplexCross (polygon.edgeVector 3) (polygon.edgeVector 0) < 0) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.quadrilateral_not_cross_pattern_one_three polygon

/--
[KWFiniteSimplePolygon.add_one_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma add_one_ne_self_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n} :
-- imply
  i + 1 ≠ i := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.add_one_ne_self polygon i

/--
[KWFiniteSimplePolygon.add_two_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma add_two_ne_self_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n} :
-- imply
  i + 2 ≠ i := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.add_two_ne_self polygon i

/--
[KWFiniteSimplePolygon.add_two_ne_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma add_two_ne_add_one_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n} :
-- imply
  i + 2 ≠ i + 1 := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.add_two_ne_add_one polygon i

/--
[KWFiniteSimplePolygon.consecutive_wbtw_of_collinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma consecutive_wbtw_of_collinear_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hcol : Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  Wbtw ℝ (polygon.vertex i) (polygon.vertex (i + 1)) (polygon.vertex (i + 2)) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.consecutive_wbtw_of_collinear polygon i hcol

/--
[KWFiniteSimplePolygon.not_sbtw_zero_two_of_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma not_sbtw_zero_two_of_between_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {k : Fin n}
-- given
  (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1) (polygon.vertex 2))
  (hk0 : k ≠ 0)
  (hk1 : k ≠ 1)
  (hk2 : k ≠ 2) :
-- imply
  ¬Sbtw ℝ (polygon.vertex 0) (polygon.vertex k) (polygon.vertex 2) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.not_sbtw_zero_two_of_between polygon hbetween k hk0 hk1 hk2

/--
[KWFiniteSimplePolygon.diagonal_zero_two_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma diagonal_zero_two_disjoint_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {k : Fin n}
-- given
  (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1) (polygon.vertex 2))
  (hk0 : k ≠ 0)
  (hk1 : k ≠ 1) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (polygon.vertex 0) z (polygon.vertex 2)} {z : ℂ | Sbtw ℝ (polygon.vertex k) z (polygon.vertex (k + 1))} := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.diagonal_zero_two_disjoint polygon hbetween k hk0 hk1

/--
[KWFiniteSimplePolygon.vertexOneRemovalIsSimple_of_diagonalIsClean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOneRemovalIsSimple_of_diagonalIsClean_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hclean : polygon.VertexOneDiagonalIsClean) :
-- imply
  polygon.VertexOneRemovalIsSimple := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneRemovalIsSimple_of_diagonalIsClean polygon hclean

/--
[KWFiniteSimplePolygon.outerTurns_ne_pi_of_diagonalIsClean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma outerTurns_ne_pi_of_diagonalIsClean_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hclean : polygon.VertexOneDiagonalIsClean) :
-- imply
  (Complex.arg (polygon.edgeVector 0 + polygon.edgeVector 1) : Real.Angle) - (Complex.arg (polygon.edgeVector (-1)) : Real.Angle) ≠ (Real.pi : Real.Angle) ∧ (Complex.arg (polygon.edgeVector 2) : Real.Angle) - (Complex.arg (polygon.edgeVector 0 + polygon.edgeVector 1) : Real.Angle) ≠ (Real.pi : Real.Angle) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.outerTurns_ne_pi_of_diagonalIsClean hm polygon hclean

/--
[KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOneDiagonalIsClean_of_between_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1) (polygon.vertex 2)) :
-- imply
  polygon.VertexOneDiagonalIsClean := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneDiagonalIsClean_of_between polygon hbetween

/--
[KWFiniteSimplePolygon.vertexOneRemovalIsSimple_of_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOneRemovalIsSimple_of_between_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hbetween : Wbtw ℝ (polygon.vertex 0) (polygon.vertex 1) (polygon.vertex 2)) :
-- imply
  polygon.VertexOneRemovalIsSimple := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneRemovalIsSimple_of_between polygon hbetween

/--
[KWStraightLineEmbedding.cyclePolygon_edgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma cyclePolygon_edgeList_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {root : V}
  {p : G.Walk root root}
-- given
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ (embedding.cyclePolygon p hp).edgeList = List.ofFn fun k : Fin p.darts.length ↦ embedding.vertex (kwGraphCycleDartLoop p k).snd - embedding.vertex (kwGraphCycleDartLoop p k).fst := by
-- proof
  apply StatMech.FrontierA.KWStraightLineEmbedding.cyclePolygon_edgeList embedding p hp

/--
[KWFiniteSimplePolygon.not_collinear_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma not_collinear_three_eq
  {polygon : KWFiniteSimplePolygon 3} :
-- imply
  ¬Collinear ℝ ({polygon.vertex 0, polygon.vertex 1, polygon.vertex 2} : Set ℂ) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.not_collinear_three polygon

/--
[kwVectorPhasePath_cons_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhasePath_cons_congr_eq
  {x : ℂ}
  {left right : List ℂ}
-- given
  (h : kwVectorPhasePath left = kwVectorPhasePath right)
  (hleft : left ≠ [])
  (hright : right ≠ [])
  (hhead : left.head hleft = right.head hright) :
-- imply
  kwVectorPhasePath (x :: left) = kwVectorPhasePath (x :: right) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_cons_congr h hleft hright hhead

/--
[kwVectorTurnPhase_ear_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorTurnPhase_ear_splice_eq
  {previous incoming outgoing next : ℂ}
-- given
  (hp : previous ≠ 0)
  (hi : incoming ≠ 0)
  (ho : outgoing ≠ 0)
  (hn : next ≠ 0)
  (hmiddle : kwComplexCross incoming outgoing ≠ 0)
  (hrightTurn : (Complex.arg next : Real.Angle) - (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
  (hleft : (0 < kwComplexCross previous incoming ∧ 0 < kwComplexCross previous (incoming + outgoing)) ∨ (kwComplexCross previous incoming < 0 ∧ kwComplexCross previous (incoming + outgoing) < 0))
  (hright : (0 < kwComplexCross (incoming + outgoing) outgoing ∧ 0 < kwComplexCross (incoming + outgoing) next) ∨ (kwComplexCross (incoming + outgoing) outgoing < 0 ∧ kwComplexCross (incoming + outgoing) next < 0)) :
-- imply
  kwVectorTurnPhase previous incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing next = kwVectorTurnPhase previous (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) next := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_ear_splice previous incoming outgoing next hp hi ho hn hmiddle hrightTurn hleft hright

/--
[kwVectorTurnPhase_straight_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorTurnPhase_straight_splice_eq
  {previous incoming outgoing next : ℂ}
-- given
  (houtgoing : (Complex.arg outgoing : Real.Angle) = (Complex.arg incoming : Real.Angle))
  (hdiagonal : (Complex.arg (incoming + outgoing) : Real.Angle) = (Complex.arg incoming : Real.Angle)) :
-- imply
  kwVectorTurnPhase previous incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing next = kwVectorTurnPhase previous (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) next := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_straight_splice previous incoming outgoing next houtgoing hdiagonal

/--
[kwVectorTurnPhase_straight_splice_of_sameRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorTurnPhase_straight_splice_of_sameRay_eq
  {previous incoming outgoing next : ℂ}
-- given
  (hi : incoming ≠ 0)
  (ho : outgoing ≠ 0)
  (hsame : SameRay ℝ incoming outgoing) :
-- imply
  kwVectorTurnPhase previous incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing next = kwVectorTurnPhase previous (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) next := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_straight_splice_of_sameRay previous incoming outgoing next hi ho hsame

/--
[KWFiniteSimplePolygon.straight_local_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma straight_local_phase_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hbetween : Wbtw ℝ (polygon.vertex i) (polygon.vertex (i + 1)) (polygon.vertex (i + 2))) :
-- imply
  kwVectorTurnPhase (polygon.edgeVector (i - 1)) (polygon.edgeVector i) * kwVectorTurnPhase (polygon.edgeVector i) (polygon.edgeVector (i + 1)) * kwVectorTurnPhase (polygon.edgeVector (i + 1)) (polygon.edgeVector (i + 2)) = kwVectorTurnPhase (polygon.edgeVector (i - 1)) (polygon.edgeVector i + polygon.edgeVector (i + 1)) * kwVectorTurnPhase (polygon.edgeVector i + polygon.edgeVector (i + 1)) (polygon.edgeVector (i + 2)) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.straight_local_phase polygon i hbetween

/--
[KWFiniteSimplePolygon.collinear_local_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma collinear_local_phase_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
  {i : Fin n}
-- given
  (hcol : Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  kwVectorTurnPhase (polygon.edgeVector (i - 1)) (polygon.edgeVector i) * kwVectorTurnPhase (polygon.edgeVector i) (polygon.edgeVector (i + 1)) * kwVectorTurnPhase (polygon.edgeVector (i + 1)) (polygon.edgeVector (i + 2)) = kwVectorTurnPhase (polygon.edgeVector (i - 1)) (polygon.edgeVector i + polygon.edgeVector (i + 1)) * kwVectorTurnPhase (polygon.edgeVector i + polygon.edgeVector (i + 1)) (polygon.edgeVector (i + 2)) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.collinear_local_phase polygon i hcol

/--
[KWFiniteSimplePolygon.removeVertexOne_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma removeVertexOne_vertex_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hsimple : polygon.VertexOneRemovalIsSimple) :
-- imply
  (polygon.removeVertexOne hm hsimple).vertex = kwRemoveVertexOne polygon.vertex := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.removeVertexOne_vertex hm polygon hsimple

/--
[KWFiniteSimplePolygon.removeVertexOne_edgeList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma removeVertexOne_edgeList_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hsimple : polygon.VertexOneRemovalIsSimple) :
-- imply
  (polygon.removeVertexOne hm hsimple).edgeList = (polygon.edgeVector 0 + polygon.edgeVector 1) :: List.ofFn (fun i : Fin (m + 1) ↦ polygon.edgeVector i.succ.succ) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.removeVertexOne_edgeList hm polygon hsimple

/--
[kwAngleTurnNoWrap_or_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwAngleTurnNoWrap_or_wrap_eq
  {a b c : Real.Angle}
-- given
  (hab : b - a ≠ (Real.pi : Real.Angle))
  (hbc : c - b ≠ (Real.pi : Real.Angle))
  (hac : c - a ≠ (Real.pi : Real.Angle)) :
-- imply
  kwAngleTurnNoWrap a b c ∨ kwAngleTurnWrap a b c := by
-- proof
  apply StatMech.FrontierA.kwAngleTurnNoWrap_or_wrap a b c hab hbc hac

/--
[KWFiniteSimplePolygon.rotated_vertexOneCrossEar_of_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma rotated_vertexOneCrossEar_of_sign_eq
  {polygon : KWFiniteSimplePolygon 4}
  {i : Fin 4}
-- given
  (hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ))
  (hsign : (0 < kwComplexCross (polygon.edgeVector (i + 3)) (polygon.edgeVector i) ∧ 0 < kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) ∧ 0 < kwComplexCross (polygon.edgeVector (i + 2)) (polygon.edgeVector (i + 3))) ∨ (kwComplexCross (polygon.edgeVector (i + 3)) (polygon.edgeVector i) < 0 ∧ kwComplexCross (polygon.edgeVector i) (polygon.edgeVector (i + 1)) < 0 ∧ kwComplexCross (polygon.edgeVector (i + 2)) (polygon.edgeVector (i + 3)) < 0)) :
-- imply
  (polygon.rotate i).VertexOneCrossEar := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.rotated_vertexOneCrossEar_of_sign polygon hnoncollinear i hsign

/--
[KWFiniteSimplePolygon.exists_rotated_vertexOneCrossEar_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma exists_rotated_vertexOneCrossEar_four_eq
  {polygon : KWFiniteSimplePolygon 4}
-- given
  (hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  ∃ r : Fin 4, (polygon.rotate r).VertexOneCrossEar := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_rotated_vertexOneCrossEar_four polygon hnoncollinear

/--
[KWFiniteSimplePolygon.vertexOneDiagonalIsClean_four_of_crossEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOneDiagonalIsClean_four_of_crossEar_eq
  {polygon : KWFiniteSimplePolygon 4}
-- given
  (hear : polygon.VertexOneCrossEar) :
-- imply
  polygon.VertexOneDiagonalIsClean := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneDiagonalIsClean_four_of_crossEar polygon hear

/--
[KWFiniteSimplePolygon.vertexOnePhaseEar_of_crossEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOnePhaseEar_of_crossEar_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hear : polygon.VertexOneCrossEar) :
-- imply
  polygon.VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOnePhaseEar_of_crossEar hm polygon hear

/--
[KWFiniteSimplePolygon.vertexOnePhaseEar_of_alignedSideEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOnePhaseEar_of_alignedSideEar_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ))
  (hear : polygon.VertexOneAlignedSideEar) :
-- imply
  polygon.VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOnePhaseEar_of_alignedSideEar hm polygon hnoncollinear hear

/--
[KWFiniteSimplePolygon.vertexOneGeometricEar_of_alignedSideEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOneGeometricEar_of_alignedSideEar_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ))
  (hear : polygon.VertexOneAlignedSideEar) :
-- imply
  polygon.VertexOneGeometricEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneGeometricEar_of_alignedSideEar hm polygon hnoncollinear hear

/--
[kwVectorTurnPhase_ear_splice_of_doubleNoWrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorTurnPhase_ear_splice_of_doubleNoWrap_eq
  {previous incoming outgoing next : ℂ}
-- given
  (hi : incoming ≠ 0)
  (ho : outgoing ≠ 0)
  (hmiddle : kwComplexCross incoming outgoing ≠ 0)
  (hleft : kwAngleTurnNoWrap (Complex.arg previous : Real.Angle) (Complex.arg incoming : Real.Angle) (Complex.arg (incoming + outgoing) : Real.Angle))
  (hright : kwAngleTurnNoWrap (Complex.arg (incoming + outgoing) : Real.Angle) (Complex.arg outgoing : Real.Angle) (Complex.arg next : Real.Angle)) :
-- imply
  kwVectorTurnPhase previous incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing next = kwVectorTurnPhase previous (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) next := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_ear_splice_of_doubleNoWrap previous incoming outgoing next hi ho hmiddle hleft hright

/--
[kwVectorTurnPhase_ear_splice_of_doubleWrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorTurnPhase_ear_splice_of_doubleWrap_eq
  {previous incoming outgoing next : ℂ}
-- given
  (hi : incoming ≠ 0)
  (ho : outgoing ≠ 0)
  (hmiddle : kwComplexCross incoming outgoing ≠ 0)
  (hleft : kwAngleTurnWrap (Complex.arg previous : Real.Angle) (Complex.arg incoming : Real.Angle) (Complex.arg (incoming + outgoing) : Real.Angle))
  (hright : kwAngleTurnWrap (Complex.arg (incoming + outgoing) : Real.Angle) (Complex.arg outgoing : Real.Angle) (Complex.arg next : Real.Angle)) :
-- imply
  kwVectorTurnPhase previous incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing next = kwVectorTurnPhase previous (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) next := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_ear_splice_of_doubleWrap previous incoming outgoing next hi ho hmiddle hleft hright

/--
[kwVectorTurnPhase_ear_splice_of_mixedParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorTurnPhase_ear_splice_of_mixedParity_eq
  {previous incoming outgoing next : ℂ}
-- given
  (hi : incoming ≠ 0)
  (ho : outgoing ≠ 0)
  (hmiddle : kwComplexCross incoming outgoing ≠ 0)
  (hparity : (kwAngleTurnNoWrap (Complex.arg previous : Real.Angle) (Complex.arg incoming : Real.Angle) (Complex.arg (incoming + outgoing) : Real.Angle) ∧ kwAngleTurnWrap (Complex.arg (incoming + outgoing) : Real.Angle) (Complex.arg outgoing : Real.Angle) (Complex.arg next : Real.Angle)) ∨ (kwAngleTurnWrap (Complex.arg previous : Real.Angle) (Complex.arg incoming : Real.Angle) (Complex.arg (incoming + outgoing) : Real.Angle) ∧ kwAngleTurnNoWrap (Complex.arg (incoming + outgoing) : Real.Angle) (Complex.arg outgoing : Real.Angle) (Complex.arg next : Real.Angle))) :
-- imply
  kwVectorTurnPhase previous incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing next = -(kwVectorTurnPhase previous (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) next) := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_ear_splice_of_mixedParity previous incoming outgoing next hi ho hmiddle hparity

/--
[KWFiniteSimplePolygon.vertexOnePhaseEar_of_doubleWrapEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOnePhaseEar_of_doubleWrapEar_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hear : polygon.VertexOneDoubleWrapEar) :
-- imply
  polygon.VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOnePhaseEar_of_doubleWrapEar hm polygon hear

/--
[KWFiniteSimplePolygon.vertexOnePhaseEar_of_strictParityEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOnePhaseEar_of_strictParityEar_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hear : polygon.VertexOneStrictParityEar) :
-- imply
  polygon.VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOnePhaseEar_of_strictParityEar hm polygon hear

/--
[KWFiniteSimplePolygon.vertexOneGeometricEar_of_strictParityEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOneGeometricEar_of_strictParityEar_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hear : polygon.VertexOneStrictParityEar) :
-- imply
  polygon.VertexOneGeometricEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneGeometricEar_of_strictParityEar hm polygon hear

/--
[KWFiniteSimplePolygon.vertexOneStrictParityEar_of_geometricEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOneStrictParityEar_of_geometricEar_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ))
  (hear : polygon.VertexOneGeometricEar hm) :
-- imply
  polygon.VertexOneStrictParityEar := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneStrictParityEar_of_geometricEar hm polygon hnoncollinear hear

/--
[KWFiniteSimplePolygon.vertexOneStrictParityEar_iff_geometricEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOneStrictParityEar_iff_geometricEar_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hnoncollinear : ∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  polygon.VertexOneStrictParityEar ↔ polygon.VertexOneGeometricEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOneStrictParityEar_iff_geometricEar hm polygon hnoncollinear

/--
[KWFiniteSimplePolygon.exists_rotated_vertexOneGeometricEar_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma exists_rotated_vertexOneGeometricEar_four_eq
  {polygon : KWFiniteSimplePolygon 4}
-- given
  (hnoncollinear : ∀ i : Fin 4, ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  ∃ r : Fin 4, (polygon.rotate r).VertexOneGeometricEar (by omega) := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_rotated_vertexOneGeometricEar_four polygon hnoncollinear

/--
[KWFiniteSimplePolygon.removable_of_geometricEar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma removable_of_geometricEar_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hear : polygon.VertexOneGeometricEar hm) :
-- imply
  polygon.VertexOneRemovalIsSimple ∧ polygon.VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.removable_of_geometricEar hm polygon hear

/--
[KWFiniteSimplePolygon.vertexOnePhaseEar_of_collinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma vertexOnePhaseEar_of_collinear_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hcol : Collinear ℝ ({polygon.vertex 0, polygon.vertex 1, polygon.vertex 2} : Set ℂ)) :
-- imply
  polygon.VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.vertexOnePhaseEar_of_collinear hm polygon hcol

/--
[KWFiniteSimplePolygon.exists_removable_of_exists_collinear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma exists_removable_of_exists_collinear_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hcol : ∃ i : Fin (m + 3), Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) :
-- imply
  ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_removable_of_exists_collinear hm polygon hcol

/--
[KWFiniteSimplePolygon.exists_removable_of_noncollinear_case](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma exists_removable_of_noncollinear_case_eq
-- given
  (hgeneric : ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm) :
-- imply
  ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_removable_of_noncollinear_case hgeneric

/--
[KWFiniteSimplePolygon.exists_removable_of_geometricEar_case](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma exists_removable_of_geometricEar_case_eq
-- given
  (hgeneric : ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneGeometricEar hm) :
-- imply
  ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_removable_of_geometricEar_case hgeneric

/--
[KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma exists_removable_of_geometricEar_five_plus_eq
-- given
  (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneGeometricEar (by omega)) :
-- imply
  ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_removable_of_geometricEar_five_plus hgeneric

/--
[KWFiniteSimplePolygon.exists_removable_of_alignedSideEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma exists_removable_of_alignedSideEar_five_plus_eq
-- given
  (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneAlignedSideEar) :
-- imply
  ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_removable_of_alignedSideEar_five_plus hgeneric

/--
[KWFiniteSimplePolygon.exists_removable_of_strictParityEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma exists_removable_of_strictParityEar_five_plus_eq
-- given
  (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneStrictParityEar) :
-- imply
  ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.exists_removable_of_strictParityEar_five_plus hgeneric

/--
[kwVectorPhasePath_contract_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhasePath_contract_ear_eq
  {previous incoming outgoing next : ℂ}
  {tail : List ℂ}
-- given
  (hp : previous ≠ 0)
  (hi : incoming ≠ 0)
  (ho : outgoing ≠ 0)
  (hn : next ≠ 0)
  (hmiddle : kwComplexCross incoming outgoing ≠ 0)
  (hrightTurn : (Complex.arg next : Real.Angle) - (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
  (hleft : (0 < kwComplexCross previous incoming ∧ 0 < kwComplexCross previous (incoming + outgoing)) ∨ (kwComplexCross previous incoming < 0 ∧ kwComplexCross previous (incoming + outgoing) < 0))
  (hright : (0 < kwComplexCross (incoming + outgoing) outgoing ∧ 0 < kwComplexCross (incoming + outgoing) next) ∨ (kwComplexCross (incoming + outgoing) outgoing < 0 ∧ kwComplexCross (incoming + outgoing) next < 0)) :
-- imply
  kwVectorPhasePath (previous :: incoming :: outgoing :: next :: tail) = kwVectorPhasePath (previous :: (incoming + outgoing) :: next :: tail) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_contract_ear previous incoming outgoing next tail hp hi ho hn hmiddle hrightTurn hleft hright

/--
[kwVectorPhasePath_contract_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhasePath_contract_of_local_eq
  {previous incoming outgoing next : ℂ}
  {tail : List ℂ}
-- given
  (hlocal : kwVectorTurnPhase previous incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing next = kwVectorTurnPhase previous (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) next) :
-- imply
  kwVectorPhasePath (previous :: incoming :: outgoing :: next :: tail) = kwVectorPhasePath (previous :: (incoming + outgoing) :: next :: tail) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_contract_of_local previous incoming outgoing next tail hlocal

/--
[kwVectorPhaseCycle_contract_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_contract_ear_eq
  {previous incoming outgoing next : ℂ}
  {tail : List ℂ}
-- given
  (hp : previous ≠ 0)
  (hi : incoming ≠ 0)
  (ho : outgoing ≠ 0)
  (hn : next ≠ 0)
  (hmiddle : kwComplexCross incoming outgoing ≠ 0)
  (hrightTurn : (Complex.arg next : Real.Angle) - (Complex.arg outgoing : Real.Angle) ≠ (Real.pi : Real.Angle))
  (hleft : (0 < kwComplexCross previous incoming ∧ 0 < kwComplexCross previous (incoming + outgoing)) ∨ (kwComplexCross previous incoming < 0 ∧ kwComplexCross previous (incoming + outgoing) < 0))
  (hright : (0 < kwComplexCross (incoming + outgoing) outgoing ∧ 0 < kwComplexCross (incoming + outgoing) next) ∨ (kwComplexCross (incoming + outgoing) outgoing < 0 ∧ kwComplexCross (incoming + outgoing) next < 0)) :
-- imply
  kwVectorPhaseCycle (previous :: incoming :: outgoing :: next :: tail) = kwVectorPhaseCycle (previous :: (incoming + outgoing) :: next :: tail) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_contract_ear previous incoming outgoing next tail hp hi ho hn hmiddle hrightTurn hleft hright

/--
[kwVectorPhaseCycle_contract_of_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_contract_of_local_eq
  {previous incoming outgoing next : ℂ}
  {tail : List ℂ}
-- given
  (hlocal : kwVectorTurnPhase previous incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing next = kwVectorTurnPhase previous (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) next) :
-- imply
  kwVectorPhaseCycle (previous :: incoming :: outgoing :: next :: tail) = kwVectorPhaseCycle (previous :: (incoming + outgoing) :: next :: tail) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_contract_of_local previous incoming outgoing next tail hlocal

/--
[KWVectorEarDecomposition.expand_front](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma expand_front_eq
  {incoming outgoing next : ℂ}
  {tail : List ℂ}
  {previous : ℂ}
-- given
  (hlocal : kwVectorTurnPhase previous incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing next = kwVectorTurnPhase previous (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) next)
  (hreduced : KWVectorEarDecomposition ((incoming + outgoing) :: next :: tail ++ [previous])) :
-- imply
  KWVectorEarDecomposition (incoming :: outgoing :: next :: tail ++ [previous]) := by
-- proof
  apply StatMech.FrontierA.KWVectorEarDecomposition.expand_front incoming outgoing next tail previous hlocal hreduced

/--
[KWVectorEarDecomposition.of_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma of_rotate_eq
  {edges : List ℂ}
  {r : ℕ}
-- given
  (h : KWVectorEarDecomposition (edges.rotate r)) :
-- imply
  KWVectorEarDecomposition edges := by
-- proof
  apply StatMech.FrontierA.KWVectorEarDecomposition.of_rotate edges r h

/--
[KWVectorEarDecomposition.expand_front_remaining](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma expand_front_remaining_eq
  {incoming outgoing : ℂ}
  {remaining : List ℂ}
-- given
  (hne : remaining ≠ [])
  (htail : remaining.tail ≠ [])
  (hlocal : kwVectorTurnPhase (remaining.tail.getLast htail) incoming * kwVectorTurnPhase incoming outgoing * kwVectorTurnPhase outgoing (remaining.head hne) = kwVectorTurnPhase (remaining.tail.getLast htail) (incoming + outgoing) * kwVectorTurnPhase (incoming + outgoing) (remaining.head hne))
  (hreduced : KWVectorEarDecomposition ((incoming + outgoing) :: remaining)) :
-- imply
  KWVectorEarDecomposition (incoming :: outgoing :: remaining) := by
-- proof
  apply StatMech.FrontierA.KWVectorEarDecomposition.expand_front_remaining incoming outgoing remaining hne htail hlocal hreduced

/--
[KWVectorEarDecomposition.of_removeVertexOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma of_removeVertexOne_eq
  {m : ℕ}
  {vertex : Fin (m + 3) → ℂ}
-- given
  (hm : 1 ≤ m)
  (hlocal : let remaining := List.ofFn (fun i : Fin (m + 1) ↦ kwCyclicEdgeVector vertex i.succ.succ) kwVectorTurnPhase (remaining.tail.getLast (by simp [remaining]; omega)) (kwCyclicEdgeVector vertex 0) * kwVectorTurnPhase (kwCyclicEdgeVector vertex 0) (kwCyclicEdgeVector vertex 1) * kwVectorTurnPhase (kwCyclicEdgeVector vertex 1) (remaining.head (by simp [remaining])) = kwVectorTurnPhase (remaining.tail.getLast (by simp [remaining]; omega)) (kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1) * kwVectorTurnPhase (kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1) (remaining.head (by simp [remaining])))
  (hreduced : KWVectorEarDecomposition (kwCyclicEdgeList (kwRemoveVertexOne vertex))) :
-- imply
  KWVectorEarDecomposition (kwCyclicEdgeList vertex) := by
-- proof
  apply StatMech.FrontierA.KWVectorEarDecomposition.of_removeVertexOne hm vertex hlocal hreduced

/--
[KWFiniteSimplePolygon.earDecomposition_of_removeVertexOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma earDecomposition_of_removeVertexOne_eq
  {m : ℕ}
  {polygon : KWFiniteSimplePolygon (m + 3)}
-- given
  (hm : 1 ≤ m)
  (hsimple : polygon.VertexOneRemovalIsSimple)
  (hphase : polygon.VertexOnePhaseEar hm)
  (hreduced : KWVectorEarDecomposition (polygon.removeVertexOne hm hsimple).edgeList) :
-- imply
  KWVectorEarDecomposition polygon.edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.earDecomposition_of_removeVertexOne hm polygon hsimple hphase hreduced

/--
[KWFiniteSimplePolygon.earDecomposition_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma earDecomposition_three_eq
  {polygon : KWFiniteSimplePolygon 3} :
-- imply
  KWVectorEarDecomposition polygon.edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.earDecomposition_three polygon

/--
[KWFiniteSimplePolygon.earDecomposition_of_exists_removable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma earDecomposition_of_exists_removable_eq
-- given
  (hexists : ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm) :
-- imply
  ∀ (k : ℕ) (polygon : KWFiniteSimplePolygon (k + 3)), KWVectorEarDecomposition polygon.edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.earDecomposition_of_exists_removable hexists

/--
[KWFiniteSimplePolygon.earDecomposition_of_exists_removable_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma earDecomposition_of_exists_removable_all_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hexists : ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm) :
-- imply
  KWVectorEarDecomposition polygon.edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.earDecomposition_of_exists_removable_all hexists polygon

/--
[KWFiniteSimplePolygon.earDecomposition_of_geometricEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma earDecomposition_of_geometricEar_five_plus_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneGeometricEar (by omega)) :
-- imply
  KWVectorEarDecomposition polygon.edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.earDecomposition_of_geometricEar_five_plus hgeneric polygon

/--
[KWFiniteSimplePolygon.earDecomposition_of_alignedSideEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma earDecomposition_of_alignedSideEar_five_plus_eq
  {n : ℕ}
  [NeZero n]
  {polygon : KWFiniteSimplePolygon n}
-- given
  (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneAlignedSideEar) :
-- imply
  KWVectorEarDecomposition polygon.edgeList := by
-- proof
  apply StatMech.FrontierA.KWFiniteSimplePolygon.earDecomposition_of_alignedSideEar_five_plus hgeneric polygon

/--
[kwVectorPhaseCycle_triangle_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_triangle_eq_neg_one_eq
  {x y z : ℂ}
-- given
  (hx : x ≠ 0)
  (hy : y ≠ 0)
  (hz : z ≠ 0)
  (hsum : x + y + z = 0)
  (hcross : kwComplexCross x y ≠ 0) :
-- imply
  kwVectorPhaseCycle [x, y, z] = -1 := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_triangle_eq_neg_one x y z hx hy hz hsum hcross

/--
[KWVectorEarDecomposition.phaseCycle_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma phaseCycle_eq_neg_one_eq
  {edges : List ℂ}
-- given
  (h : KWVectorEarDecomposition edges) :
-- imply
  kwVectorPhaseCycle edges = -1 := by
-- proof
  apply StatMech.FrontierA.KWVectorEarDecomposition.phaseCycle_eq_neg_one h

/--
[KWStraightLineCycleEarDecomposition.of_exists_removable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma of_exists_removable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hexists : ∀ (m : ℕ) (hm : 1 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneRemovalIsSimple ∧ (polygon.rotate r).VertexOnePhaseEar hm) :
-- imply
  KWStraightLineCycleEarDecomposition G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleEarDecomposition.of_exists_removable hexists embedding

/--
[KWStraightLineCycleEarDecomposition.of_geometricEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma of_geometricEar_five_plus_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hgeneric : ∀ (m : ℕ) (hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneGeometricEar (by omega)) :
-- imply
  KWStraightLineCycleEarDecomposition G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleEarDecomposition.of_geometricEar_five_plus hgeneric embedding

/--
[KWStraightLineCycleEarDecomposition.of_alignedSideEar_five_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma of_alignedSideEar_five_plus_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
-- given
  (hgeneric : ∀ (m : ℕ) (_hm : 2 ≤ m) (polygon : KWFiniteSimplePolygon (m + 3)), (∀ i : Fin (m + 3), ¬Collinear ℝ ({polygon.vertex i, polygon.vertex (i + 1), polygon.vertex (i + 2)} : Set ℂ)) → ∃ r : Fin (m + 3), (polygon.rotate r).VertexOneAlignedSideEar) :
-- imply
  KWStraightLineCycleEarDecomposition G embedding := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleEarDecomposition.of_alignedSideEar_five_plus hgeneric embedding

/--
[KWStraightLineCycleEarDecomposition.phaseProduct_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean)
-/
@[path]
private lemma phaseProduct_eq_neg_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {embedding : KWStraightLineEmbedding G}
  {root : V}
  {p : G.Walk root root}
-- given
  (h : KWStraightLineCycleEarDecomposition G embedding)
  (hp : p.IsCycle) :
-- imply
  letI : NeZero p.darts.length := ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩ kwLoopPhaseProduct embedding.turnPhase (kwGraphCycleDartLoop p) = -1 := by
-- proof
  apply StatMech.FrontierA.KWStraightLineCycleEarDecomposition.phaseProduct_eq_neg_one h p hp


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part7
open StatMech StatMech.FrontierA


/--
[KWRawNonbacktrackingSimpleData.halfOpenEdge_subset_closedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma halfOpenEdge_subset_closedEdge_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin n → ℂ}
  {i : Fin n}
-- given
  (h : KWRawNonbacktrackingSimpleData vertex) :
-- imply
  kwRawHalfOpenEdge vertex i ⊆ kwRawClosedEdge vertex i := by
-- proof
  apply StatMech.FrontierA.KWRawNonbacktrackingSimpleData.halfOpenEdge_subset_closedEdge h i

/--
[KWRawNonbacktrackingSimpleData.halfOpenEdge_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma halfOpenEdge_disjoint_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin n → ℂ}
  {i j : Fin n}
-- given
  (h : KWRawNonbacktrackingSimpleData vertex)
  (hij : i ≠ j) :
-- imply
  Disjoint (kwRawHalfOpenEdge vertex i) (kwRawHalfOpenEdge vertex j) := by
-- proof
  apply StatMech.FrontierA.KWRawNonbacktrackingSimpleData.halfOpenEdge_disjoint h hij

/--
[kwPrefixPositions_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwPrefixPositions_nil_eq :
-- imply
  kwPrefixPositions [] = [] := by
-- proof
  apply StatMech.FrontierA.kwPrefixPositions_nil

/--
[kwPrefixPositions_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwPrefixPositions_cons_eq
  {d : Fin 4}
  {tail : List (Fin 4)} :
-- imply
  kwPrefixPositions (d :: tail) = 0 :: (kwPrefixPositions tail).map (stepOf d + ·) := by
-- proof
  apply StatMech.FrontierA.kwPrefixPositions_cons d tail

/--
[kwPrefixPositions_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwPrefixPositions_length_eq
  {word : List (Fin 4)} :
-- imply
  (kwPrefixPositions word).length = word.length := by
-- proof
  apply StatMech.FrontierA.kwPrefixPositions_length word

/--
[kwPrefixPositions_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwPrefixPositions_append_eq
  {left right : List (Fin 4)} :
-- imply
  kwPrefixPositions (left ++ right) = kwPrefixPositions left ++ (kwPrefixPositions right).map (((left.map stepOf).sum) + ·) := by
-- proof
  apply StatMech.FrontierA.kwPrefixPositions_append left right

/--
[kwPrefixPositions_get](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwPrefixPositions_get_eq
  {word : List (Fin 4)}
  {k : Fin word.length} :
-- imply
  (kwPrefixPositions word).get ⟨k.val, by simpa using k.isLt⟩ = ((word.take k.val).map stepOf).sum := by
-- proof
  apply StatMech.FrontierA.kwPrefixPositions_get word k

/--
[kwListDirection_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwListDirection_ofFn_eq
  {word : List (Fin 4)} :
-- imply
  List.ofFn (kwListDirection word) = word := by
-- proof
  apply StatMech.FrontierA.kwListDirection_ofFn word

/--
[kwListDirection_pos_eq_prefixPosition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwListDirection_pos_eq_prefixPosition_eq
  {word : List (Fin 4)}
  [NeZero word.length]
  {k : Fin word.length} :
-- imply
  pos (kwListDirection word) k = (kwPrefixPositions word).get ⟨k.val, by simpa using k.isLt⟩ := by
-- proof
  apply StatMech.FrontierA.kwListDirection_pos_eq_prefixPosition word k

/--
[kwListDirection_pos_injective_of_prefixPositions_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwListDirection_pos_injective_of_prefixPositions_nodup_eq
  {word : List (Fin 4)}
  [NeZero word.length]
-- given
  (h : (kwPrefixPositions word).Nodup) :
-- imply
  Function.Injective (pos (kwListDirection word)) := by
-- proof
  apply StatMech.FrontierA.kwListDirection_pos_injective_of_prefixPositions_nodup word h

/--
[kwPrefixPositions_replicate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwPrefixPositions_replicate_eq
  {d : Fin 4}
  {N : ℕ} :
-- imply
  kwPrefixPositions (List.replicate N d) = (List.range N).map (fun k ↦ k • stepOf d) := by
-- proof
  apply StatMech.FrontierA.kwPrefixPositions_replicate d N

/--
[kwPrefixPositions_replicate_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwPrefixPositions_replicate_nodup_eq
  {d : Fin 4}
  {N : ℕ} :
-- imply
  (kwPrefixPositions (List.replicate N d)).Nodup := by
-- proof
  apply StatMech.FrontierA.kwPrefixPositions_replicate_nodup d N

/--
[kwPrefixPositions_integralAxisWord_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwPrefixPositions_integralAxisWord_nodup_eq
  {v : ℤ × ℤ}
-- given
  (haxis : v.1 = 0 ∨ v.2 = 0) :
-- imply
  (kwPrefixPositions (kwIntegralAxisWord v)).Nodup := by
-- proof
  apply StatMech.FrontierA.kwPrefixPositions_integralAxisWord_nodup haxis

/--
[kwIntComplex_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntComplex_zero_eq :
-- imply
  kwIntComplex 0 = 0 := by
-- proof
  apply StatMech.FrontierA.kwIntComplex_zero

/--
[kwIntComplex_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntComplex_add_eq
  {p q : ℤ × ℤ} :
-- imply
  kwIntComplex (p + q) = kwIntComplex p + kwIntComplex q := by
-- proof
  apply StatMech.FrontierA.kwIntComplex_add p q

/--
[kwIntComplex_nsmul_stepOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntComplex_nsmul_stepOf_eq
  {d : Fin 4}
  {k : ℕ} :
-- imply
  kwIntComplex (k • stepOf d) = (k : ℝ) * kwRectilinearVector d := by
-- proof
  apply StatMech.FrontierA.kwIntComplex_nsmul_stepOf d k

/--
[kwIntegralPolygonEdgePoints_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntegralPolygonEdgePoints_length_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
  {i : Fin n} :
-- imply
  (kwIntegralPolygonEdgePoints p i).length = (kwIntegralPolygonEdgeWord p i).length := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonEdgePoints_length p i

/--
[kwIntegralPolygonEdgePoints_nodup_of_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntegralPolygonEdgePoints_nodup_of_axis_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
  {i : Fin n}
-- given
  (haxis : (p (i + 1) - p i).1 = 0 ∨ (p (i + 1) - p i).2 = 0) :
-- imply
  (kwIntegralPolygonEdgePoints p i).Nodup := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonEdgePoints_nodup_of_axis p i haxis

/--
[kwIntegralPolygonEdgePoints_complex_mem_halfOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntegralPolygonEdgePoints_complex_mem_halfOpen_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
  {i : Fin n}
  {q : ℤ × ℤ}
-- given
  (haxis : (p (i + 1) - p i).1 = 0 ∨ (p (i + 1) - p i).2 = 0)
  (hq : q ∈ kwIntegralPolygonEdgePoints p i) :
-- imply
  kwIntComplex q ∈ kwRawHalfOpenEdge (fun j ↦ kwIntComplex (p j)) i := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonEdgePoints_complex_mem_halfOpen p i haxis hq

/--
[kwPrefixPositions_flatten_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwPrefixPositions_flatten_map_eq
  {start : ℕ → ℤ × ℤ}
  {blocks : List (List (Fin 4))}
-- given
  (hstep : ∀ k (hk : k < blocks.length), (((blocks[k]'hk).map stepOf).sum) = start (k + 1) - start k) :
-- imply
  (kwPrefixPositions blocks.flatten).map (start 0 + ·) = kwIndexedPrefixBlocks start blocks := by
-- proof
  apply StatMech.FrontierA.kwPrefixPositions_flatten_map start blocks hstep

/--
[kwCyclicIntegralVertex_fin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwCyclicIntegralVertex_fin_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
  {i : Fin n} :
-- imply
  kwCyclicIntegralVertex p i.val = p i := by
-- proof
  apply StatMech.FrontierA.kwCyclicIntegralVertex_fin p i

/--
[kwCyclicIntegralVertex_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwCyclicIntegralVertex_succ_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
  {i : Fin n} :
-- imply
  kwCyclicIntegralVertex p (i.val + 1) = p (i + 1) := by
-- proof
  apply StatMech.FrontierA.kwCyclicIntegralVertex_succ p i

/--
[kwIndexedPrefixBlocks_integralPolygon](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIndexedPrefixBlocks_integralPolygon_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ} :
-- imply
  kwIndexedPrefixBlocks (kwCyclicIntegralVertex p) (List.ofFn (kwIntegralPolygonEdgeWord p)) = kwIntegralPolygonPointList p := by
-- proof
  apply StatMech.FrontierA.kwIndexedPrefixBlocks_integralPolygon p

/--
[kwIntegralPolygonPointList_eq_prefixPositions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntegralPolygonPointList_eq_prefixPositions_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ} :
-- imply
  kwIntegralPolygonPointList p = (kwPrefixPositions (kwIntegralPolygonWord p)).map (p 0 + ·) := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonPointList_eq_prefixPositions p

/--
[kwIntegralPolygonPointList_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntegralPolygonPointList_nodup_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
-- given
  (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨ (p (i + 1) - p i).2 = 0)
  (hsimple : KWRawNonbacktrackingSimpleData (fun i ↦ kwIntComplex (p i))) :
-- imply
  (kwIntegralPolygonPointList p).Nodup := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonPointList_nodup p haxis hsimple

/--
[kwIntegralPolygonWord_vertexCount_le_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntegralPolygonWord_vertexCount_le_length_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
-- given
  (hsimple : KWRawNonbacktrackingSimpleData (fun i ↦ kwIntComplex (p i))) :
-- imply
  n ≤ (kwIntegralPolygonWord p).length := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonWord_vertexCount_le_length p hsimple

/--
[kwIntegralPolygonDirection_pos_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntegralPolygonDirection_pos_injective_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
  [NeZero (kwIntegralPolygonWord p).length]
-- given
  (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨ (p (i + 1) - p i).2 = 0)
  (hsimple : KWRawNonbacktrackingSimpleData (fun i ↦ kwIntComplex (p i))) :
-- imply
  Function.Injective (pos (kwIntegralPolygonDirection p)) := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonDirection_pos_injective p haxis hsimple

/--
[kwIntegralPolygonDirection_phaseProduct_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntegralPolygonDirection_phaseProduct_eq_neg_one_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
  [NeZero (kwIntegralPolygonWord p).length]
-- given
  (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨ (p (i + 1) - p i).2 = 0)
  (hsimple : KWRawNonbacktrackingSimpleData (fun i ↦ kwIntComplex (p i))) :
-- imply
  (∏ k : Fin (kwIntegralPolygonWord p).length, kwVectorTurnPhase (kwRectilinearVector (kwIntegralPolygonDirection p k)) (kwRectilinearVector (kwIntegralPolygonDirection p (k + 1)))) = -1 := by
-- proof
  apply StatMech.FrontierA.kwIntegralPolygonDirection_phaseProduct_eq_neg_one p haxis hsimple

/--
[kwVectorTurnPhase_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwVectorTurnPhase_self_eq
  {z : ℂ} :
-- imply
  kwVectorTurnPhase z z = 1 := by
-- proof
  apply StatMech.FrontierA.kwVectorTurnPhase_self z

/--
[kwVectorPhasePath_replicate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwVectorPhasePath_replicate_eq
  {z : ℂ}
  {N : ℕ} :
-- imply
  kwVectorPhasePath (List.replicate N z) = 1 := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_replicate z N

/--
[kwVectorPhasePath_expandedRectilinearBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwVectorPhasePath_expandedRectilinearBlocks_eq
  {blocks : List (Fin 4 × ℕ)}
-- given
  (hpos : ∀ block ∈ blocks, 0 < block.2) :
-- imply
  kwVectorPhasePath (kwExpandedRectilinearBlocks blocks) = kwVectorPhasePath (kwCompressedRectilinearBlocks blocks) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhasePath_expandedRectilinearBlocks blocks hpos

/--
[kwExpandedRectilinearBlocks_getLastD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwExpandedRectilinearBlocks_getLastD_eq
  {blocks : List (Fin 4 × ℕ)}
  {default : ℂ}
-- given
  (hpos : ∀ block ∈ blocks, 0 < block.2) :
-- imply
  (kwExpandedRectilinearBlocks blocks).getLastD default = (kwCompressedRectilinearBlocks blocks).getLastD default := by
-- proof
  apply StatMech.FrontierA.kwExpandedRectilinearBlocks_getLastD blocks hpos default

/--
[kwVectorPhaseCycle_expandedRectilinearBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwVectorPhaseCycle_expandedRectilinearBlocks_eq
  {blocks : List (Fin 4 × ℕ)}
-- given
  (hpos : ∀ block ∈ blocks, 0 < block.2) :
-- imply
  kwVectorPhaseCycle (kwExpandedRectilinearBlocks blocks) = kwVectorPhaseCycle (kwCompressedRectilinearBlocks blocks) := by
-- proof
  apply StatMech.FrontierA.kwVectorPhaseCycle_expandedRectilinearBlocks blocks hpos

/--
[kwIntegralAxisPolygon_phaseCycle_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean)
-/
@[path]
private lemma kwIntegralAxisPolygon_phaseCycle_eq_neg_one_eq
  {n : ℕ}
  [NeZero n]
  {p : Fin n → ℤ × ℤ}
-- given
  (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨ (p (i + 1) - p i).2 = 0)
  (hsimple : KWRawNonbacktrackingSimpleData (fun i ↦ kwIntComplex (p i))) :
-- imply
  kwVectorPhaseCycle (List.ofFn fun i : Fin n ↦ kwIntComplex (p (i + 1) - p i)) = -1 := by
-- proof
  apply StatMech.FrontierA.kwIntegralAxisPolygon_phaseCycle_eq_neg_one p haxis hsimple


-- created on 2026-10-23

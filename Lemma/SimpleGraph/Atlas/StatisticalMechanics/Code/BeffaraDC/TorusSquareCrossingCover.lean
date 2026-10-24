import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusReduceSite_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusReduceSite_mk_eq
  {L : ℕ}
  {a b : ℤ} :
-- imply
  torusReduceSite L ![a, b] = ((a : ZMod L), (b : ZMod L)) := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSite_mk L a b

/--
[torusReduceSite_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusReduceSite_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  (onsTorusGraph L).Adj (torusReduceSite L x) (torusReduceSite L y) := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSite_adj L hxy

/--
[torusReduceSite_val_of_mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusReduceSite_val_of_mem_rect_eq
  {L n : ℕ}
  {x : Site 2}
-- given
  (hnL : n < L)
  (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ)) :
-- imply
  (torusReduceSite L x).1.val = Int.toNat (x 0) ∧ (torusReduceSite L x).2.val = Int.toNat (x 1) := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSite_val_of_mem_rect L n hnL hx

/--
[torusReduceSite_mem_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusReduceSite_mem_square_eq
  {L n : ℕ}
  {x : Site 2}
-- given
  (hnL : n < L)
  (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ)) :
-- imply
  torusReduceSite L x ∈ torusSquareVertexSet L n := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSite_mem_square L n hnL hx

/--
[torusPlanarHorizontalCrossing_imp_torus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusPlanarHorizontalCrossing_imp_torus_eq
  {L n : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
-- given
  (hnL : n < L)
  (h : HorizontalCrossing (torusPlanarPullback L omega) 0 (n : ℤ) 0 (n : ℤ)) :
-- imply
  torusSquareHorizontalCrossing L n omega := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarHorizontalCrossing_imp_torus L n hnL omega h

/--
[torus_not_horizontal_imp_planar_not_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torus_not_horizontal_imp_planar_not_horizontal_eq
  {L n : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
-- given
  (hnL : n < L)
  (h : ¬ torusSquareHorizontalCrossing L n omega) :
-- imply
  ¬ HorizontalCrossing (torusPlanarPullback L omega) 0 (n : ℤ) 0 (n : ℤ) := by
-- proof
  apply StatMech.BeffaraDC.torus_not_horizontal_imp_planar_not_horizontal L n hnL omega h

/--
[torusReduceSwapSite_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusReduceSwapSite_mk_eq
  {L : ℕ}
  {a b : ℤ} :
-- imply
  torusReduceSwapSite L ![a, b] = ((b : ZMod L), (a : ZMod L)) := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSwapSite_mk L a b

/--
[torusReduceSwapSite_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusReduceSwapSite_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : Site 2}
-- given
  (hxy : (hypercubicLattice 2).Adj x y) :
-- imply
  (onsTorusGraph L).Adj (torusReduceSwapSite L x) (torusReduceSwapSite L y) := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSwapSite_adj L hxy

/--
[torusPlanarPullback_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusPlanarPullback_horizontal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {a b : ℤ} :
-- imply
  torusPlanarPullback L omega s(![a, b], ![a + 1, b]) = omega (torusHorizontalEdge L (a : ZMod L) (b : ZMod L)) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPullback_horizontal L omega a b

/--
[torusPlanarPullback_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusPlanarPullback_vertical_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {a b : ℤ} :
-- imply
  torusPlanarPullback L omega s(![a, b], ![a, b + 1]) = omega (torusVerticalEdge L (a : ZMod L) (b : ZMod L)) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarPullback_vertical L omega a b

/--
[torusAmbientSwapEdgeEquiv_symm_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusAmbientSwapEdgeEquiv_symm_horizontal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusAmbientSwapEdgeEquiv L).symm (torusHorizontalEdge L x y) = torusVerticalEdge L y x := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientSwapEdgeEquiv_symm_horizontal L x y

/--
[torusAmbientSwapEdgeEquiv_symm_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusAmbientSwapEdgeEquiv_symm_vertical_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : ZMod L} :
-- imply
  (torusAmbientSwapEdgeEquiv L).symm (torusVerticalEdge L x y) = torusHorizontalEdge L y x := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientSwapEdgeEquiv_symm_vertical L x y

/--
[torusAmbientSwapCellDual_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusAmbientSwapCellDual_horizontal_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {x y : ZMod L} :
-- imply
  torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega) (torusHorizontalEdge L x y) = !(omega (torusHorizontalEdge L y (x + 1))) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientSwapCellDual_horizontal L omega x y

/--
[torusAmbientSwapCellDual_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusAmbientSwapCellDual_vertical_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
  {x y : ZMod L} :
-- imply
  torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega) (torusVerticalEdge L x y) = !(omega (torusVerticalEdge L (y + 1) x)) := by
-- proof
  apply StatMech.BeffaraDC.torusAmbientSwapCellDual_vertical L omega x y

/--
[torus_walk_first_hit_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torus_walk_first_hit_down_eq
  {eta : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {p : (openSubgraph 2 eta).Walk x y}
  {i : Fin 2}
  {t : ℤ}
-- given
  (hx : t < x i)
  (hy : y i ≤ t) :
-- imply
  ∃ j ≤ p.length, (p.getVert j) i = t ∧ ∀ m < j, t < (p.getVert m) i := by
-- proof
  apply StatMech.BeffaraDC.torus_walk_first_hit_down p i t hx hy

/--
[torus_faceBand_verticalCrossing_to_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torus_faceBand_verticalCrossing_to_square_eq
  {eta : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 < n)
  (h : VerticalCrossing eta 0 (n - 1) (-1) n) :
-- imply
  VerticalCrossing eta 0 n 0 n := by
-- proof
  apply StatMech.BeffaraDC.torus_faceBand_verticalCrossing_to_square hn h

/--
[torusReduceSwapSite_mem_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusReduceSwapSite_mem_square_eq
  {L n : ℕ}
  {x : Site 2}
-- given
  (hnL : n < L)
  (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ)) :
-- imply
  torusReduceSwapSite L x ∈ torusSquareVertexSet L n := by
-- proof
  apply StatMech.BeffaraDC.torusReduceSwapSite_mem_square L n hnL hx

/--
[torusPlanarFaceVerticalCrossing_imp_rotatedTorusHorizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torusPlanarFaceVerticalCrossing_imp_rotatedTorusHorizontal_eq
  {L n : ℕ}
  [Fact (2 < L)]
  {omega : TorusAmbientConfig L}
-- given
  (hnL : n < L)
  (h : VerticalCrossing (fci_faceDualConfig (torusPlanarPullback L omega)) 0 (n : ℤ) 0 (n : ℤ)) :
-- imply
  torusSquareHorizontalCrossing L n (torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega)) := by
-- proof
  apply StatMech.BeffaraDC.torusPlanarFaceVerticalCrossing_imp_rotatedTorusHorizontal L n hnL omega h

/--
[torus_concreteSquareCrossing_dual_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torus_concreteSquareCrossing_dual_cover_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  {omega : TorusAmbientConfig L}
-- given
  (hn : 1 ≤ n)
  (hnL : n < L)
  (hno : ¬ torusSquareHorizontalCrossing L n omega) :
-- imply
  torusCellDualAmbientConfig L omega ∈ torusSquareVerticalCrossingEvent L n := by
-- proof
  apply StatMech.BeffaraDC.torus_concreteSquareCrossing_dual_cover L n hn hnL omega hno

/--
[torus_concreteSquareCrossing_ge_one_div_one_add_q_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean)
-/
@[path]
private lemma torus_concreteSquareCrossing_ge_one_div_one_add_q_unconditional_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  {q : ℝ}
-- given
  (hn : 1 ≤ n)
  (hnL : n < L)
  (hq1 : 1 ≤ q) :
-- imply
  1 / (1 + q) ≤ torusAmbientEventProbability L (selfDualPoint q) q (torusSquareHorizontalCrossingEvent L n) := by
-- proof
  apply StatMech.BeffaraDC.torus_concreteSquareCrossing_ge_one_div_one_add_q_unconditional L n hn hnL hq1


-- created on 2026-10-23

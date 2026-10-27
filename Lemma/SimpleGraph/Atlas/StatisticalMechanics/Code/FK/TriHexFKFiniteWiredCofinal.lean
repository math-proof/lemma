import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
open Finset Set SimpleGraph Filter MeasureTheory Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triangular_mem_orbitBox_iff_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triangular_mem_orbitBox_iff_box_eq
  {n : Nat}
  {v : Site 2} :
-- imply
  v ∈ triangular.orbitBox n ↔ v ∈ box 2 n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_mem_orbitBox_iff_box n v

/--
[hexagonal_mem_orbitBox_iff_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma hexagonal_mem_orbitBox_iff_box_eq
  {n : Nat}
  {v : HexVertex} :
-- imply
  v ∈ hexagonal.orbitBox n ↔ v.1 ∈ box 2 n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_mem_orbitBox_iff_box n v

/--
[triHexPlanarCellTerminal_mem_box_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarCellTerminal_mem_box_succ_eq
  {n : Nat}
  {z : Site 2}
  {i : Fin 3}
-- given
  (hz : z ∈ box 2 n) :
-- imply
  triHexPlanarCellTerminal z i ∈ box 2 (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarCellTerminal_mem_box_succ n hz i

/--
[triHexPlanarCellPredecessor_mem_box_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarCellPredecessor_mem_box_succ_eq
  {n : Nat}
  {v : Site 2}
-- given
  (hv : v ∈ box 2 n) :
-- imply
  v - hexagonalStep 0 ∈ box 2 (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarCellPredecessor_mem_box_succ n hv

/--
[triHexPlanarFiniteStarVertexEmbedding_cell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarVertexEmbedding_cell_eq
  {n : Nat}
  {z : TriHexPlanarFiniteCell n} :
-- imply
  triHexPlanarFiniteStarVertexEmbedding n (Sum.inl z) = (z.1, false) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarVertexEmbedding_cell n z

/--
[triHexPlanarFiniteStarVertexEmbedding_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarVertexEmbedding_terminal_eq
  {n : Nat}
  {v : TriHexPlanarFiniteTerminal n} :
-- imply
  triHexPlanarFiniteStarVertexEmbedding n (Sum.inr v) = (v.1, true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarVertexEmbedding_terminal n v

/--
[triHexPlanarFiniteStarGraph_adj_hexagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarGraph_adj_hexagonal_eq
  {n : Nat}
  {u v : TriHexPlanarFiniteStarVertex n}
-- given
  (huv : (triHexPlanarFiniteStarGraph n).Adj u v) :
-- imply
  hexagonalGraph.Adj (triHexPlanarFiniteStarVertexEmbedding n u) (triHexPlanarFiniteStarVertexEmbedding n v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarGraph_adj_hexagonal n huv

/--
[triHexPlanarFiniteStarGraph_adj_of_hexagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarGraph_adj_of_hexagonal_eq
  {n : Nat}
  {u v : TriHexPlanarFiniteStarVertex n}
-- given
  (huv : hexagonalGraph.Adj (triHexPlanarFiniteStarVertexEmbedding n u) (triHexPlanarFiniteStarVertexEmbedding n v)) :
-- imply
  (triHexPlanarFiniteStarGraph n).Adj u v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarGraph_adj_of_hexagonal n huv

/--
[triHexPlanarFiniteStarGraph_adj_iff_hexagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarGraph_adj_iff_hexagonal_eq
  {n : Nat}
  {u v : TriHexPlanarFiniteStarVertex n} :
-- imply
  (triHexPlanarFiniteStarGraph n).Adj u v ↔ hexagonalGraph.Adj (triHexPlanarFiniteStarVertexEmbedding n u) (triHexPlanarFiniteStarVertexEmbedding n v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarGraph_adj_iff_hexagonal n u v

/--
[triHexPlanarFiniteStar_adjMatch_hexagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_adjMatch_hexagonal_eq
  {n : Nat} :
-- imply
  ocd_AdjMatch (triHexPlanarFiniteStarGraph n) hexagonalGraph (triHexPlanarFiniteStarVertexEmbedding n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_adjMatch_hexagonal n

/--
[triHexPlanarFiniteStar_cell_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_cell_not_boundary_eq
  {n : Nat}
  {z : TriHexPlanarFiniteCell n} :
-- imply
  ¬ ∃ w : HexVertex, hexagonalGraph.Adj (triHexPlanarFiniteStarVertexEmbedding n (Sum.inl z)) w ∧ w ∉ Set.range (triHexPlanarFiniteStarVertexEmbedding n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_cell_not_boundary n z

/--
[triHexPlanarFiniteStar_terminal_boundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_terminal_boundary_iff_eq
  {n : Nat}
  {v : TriHexPlanarFiniteTerminal n} :
-- imply
  triHexPlanarFiniteStarBoundary n (Sum.inr v) ↔ ∃ w : HexVertex, hexagonalGraph.Adj (triHexPlanarFiniteStarVertexEmbedding n (Sum.inr v)) w ∧ w ∉ Set.range (triHexPlanarFiniteStarVertexEmbedding n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_terminal_boundary_iff n v

/--
[triHexPlanarFiniteStar_boundary_iff_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_boundary_iff_ambient_eq
  {n : Nat}
  {u : TriHexPlanarFiniteStarVertex n} :
-- imply
  triHexPlanarFiniteStarBoundary n u ↔ ∃ w : HexVertex, hexagonalGraph.Adj (triHexPlanarFiniteStarVertexEmbedding n u) w ∧ w ∉ Set.range (triHexPlanarFiniteStarVertexEmbedding n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_boundary_iff_ambient n u

/--
[triHexPlanarFiniteStar_range_subset_orbitBox_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_range_subset_orbitBox_succ_eq
  {n : Nat} :
-- imply
  Set.range (triHexPlanarFiniteStarVertexEmbedding n) ⊆ (hexagonal.orbitBox (n + 1) : Set HexVertex) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_range_subset_orbitBox_succ n

/--
[hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ_eq
  {n : Nat} :
-- imply
  (hexagonal.orbitBox n : Set HexVertex) ⊆ Set.range (triHexPlanarFiniteStarVertexEmbedding (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ n

/--
[triHexPlanarFiniteTerminal_subset_triangular_orbitBox_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTerminal_subset_triangular_orbitBox_succ_eq
  {n : Nat}
  {v : TriHexPlanarFiniteTerminal n} :
-- imply
  v.1 ∈ triangular.orbitBox (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTerminal_subset_triangular_orbitBox_succ n v

/--
[triangular_orbitBox_subset_triHexPlanarFiniteTerminal_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triangular_orbitBox_subset_triHexPlanarFiniteTerminal_succ_eq
  {n : Nat}
  {v : Site 2}
-- given
  (hv : v ∈ triangular.orbitBox n) :
-- imply
  v ∈ triHexPlanarFiniteTerminalFinset (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangular_orbitBox_subset_triHexPlanarFiniteTerminal_succ n hv

/--
[triangularIndexedEdge_rebase_eq_cellEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triangularIndexedEdge_rebase_eq_cellEdge_eq
  {z : Site 2}
  {i : Fin 3} :
-- imply
  triangularIndexedEdge (triHexPlanarTriangleIndexEquiv (z, i)) = s(triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal1 i), triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal2 i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularIndexedEdge_rebase_eq_cellEdge z i

/--
[triHexPlanarFiniteTriangle_adj_or_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_adj_or_boundary_eq
  {n : Nat}
  {u v : TriHexPlanarFiniteTerminal n}
-- given
  (huv : triangularGraph.Adj u.1 v.1) :
-- imply
  (triHexPlanarFiniteTriangleGraph n).Adj u v ∨ (triHexPlanarFiniteBoundary n u ∧ triHexPlanarFiniteBoundary n v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_adj_or_boundary n huv

/--
[triHexPlanarFiniteTriangle_induced_le_wiredGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_induced_le_wiredGraph_eq
  {n : Nat} :
-- imply
  SimpleGraph.comap Subtype.val triangularGraph ≤ triHexPlanarFiniteTriangleGraph n ⊔ boundaryCliqueGraph (triHexPlanarFiniteBoundary n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_induced_le_wiredGraph n

/--
[triHexPlanarFiniteTriangleGraph_le_induced](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleGraph_le_induced_eq
  {n : Nat} :
-- imply
  triHexPlanarFiniteTriangleGraph n ≤ triHexPlanarFiniteTriangleInducedGraph n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleGraph_le_induced n

/--
[triHexPlanarFiniteRoot_not_boundary_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteRoot_not_boundary_succ_eq
  {n : Nat} :
-- imply
  ¬ triHexPlanarFiniteBoundary (n + 1) (triHexPlanarFiniteTerminalMap (n + 1) (triHexPlanarFiniteRootCell (n + 1)) 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteRoot_not_boundary_succ n

/--
[triHexPlanarFiniteTriangleInducedBoundaryReachIndicator_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleInducedBoundaryReachIndicator_eq_eq
  {n : Nat}
  {eta : ConfigSpace (triHexPlanarFiniteTriangleInducedGraph (n + 1)).edgeSet} :
-- imply
  triHexPlanarFiniteTriangleInducedBoundaryReachIndicator (n + 1) eta = triHexPlanarFiniteTriangleBoundaryReachIndicator (n + 1) (activeGraphRestrict (triHexPlanarFiniteTriangleGraph (n + 1)) (triHexPlanarFiniteTriangleInducedGraph (n + 1)) (triHexPlanarFiniteTriangleGraph_le_induced (n + 1)) eta) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleInducedBoundaryReachIndicator_eq n eta

/--
[triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  triHexPlanarFiniteTriangleInducedWiredBoundaryProbability (n + 1) p q = triHexPlanarFiniteTriangleWiredBoundaryProbability (n + 1) p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq n hp hp1 hq

/--
[triHexPlanarFiniteInducedWiredBoundaryProbability_eq_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteInducedWiredBoundaryProbability_eq_homogeneous_eq
  {n : Nat}
  {q p : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Set.Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  triHexPlanarFiniteStarWiredBoundaryProbability (n + 1) (BeffaraDC.dualParam p q) q = triHexPlanarFiniteTriangleInducedWiredBoundaryProbability (n + 1) p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteInducedWiredBoundaryProbability_eq_homogeneous n hq hp hsurface

/--
[triHexPlanarFiniteStarToHexBuffered_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarToHexBuffered_adjMatch_eq
  {n : Nat} :
-- imply
  ocd_AdjMatch (triHexPlanarFiniteStarGraph n) (hexagonal.bufferedGraph (n + 2)) (triHexPlanarFiniteStarToHexBuffered n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarToHexBuffered_adjMatch n

/--
[triHexPlanarFiniteStarToHexBuffered_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarToHexBuffered_not_boundary_eq
  {n : Nat}
  {v : TriHexPlanarFiniteStarVertex n} :
-- imply
  ¬ hexagonal.bufferedBoundary (n + 2) (triHexPlanarFiniteStarToHexBuffered n v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarToHexBuffered_not_boundary n v

/--
[triHexPlanarFiniteStar_boundary_of_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_boundary_of_outsideGraph_adj_eq
  {n : Nat}
  {psi : ConfigSpace (Sym2 (hexagonal.BufferedVertex (n + 2)))}
  {x : TriHexPlanarFiniteStarVertex n}
  {c : hexagonal.BufferedVertex (n + 2)}
-- given
  (h : (ocd_outsideGraph (hexagonal.bufferedGraph (n + 2)) (triHexPlanarFiniteStarToHexBuffered n) (hexagonal.bufferedBoundary (n + 2)) psi).Adj (triHexPlanarFiniteStarToHexBuffered n x) c) :
-- imply
  triHexPlanarFiniteStarBoundary n x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_boundary_of_outsideGraph_adj n psi x h

/--
[triHexPlanarFiniteStar_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_inducedWiring_le_eq
  {n : Nat}
  {psi : ConfigSpace (Sym2 (hexagonal.BufferedVertex (n + 2)))} :
-- imply
  ocd_inducedWiring (hexagonal.bufferedGraph (n + 2)) (triHexPlanarFiniteStarToHexBuffered n) (hexagonal.bufferedBoundary (n + 2)) psi ≤ boundaryCliqueGraph (triHexPlanarFiniteStarBoundary n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_inducedWiring_le n psi

/--
[triHexPlanarFiniteStar_outerBuffered_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_outerBuffered_dominated_eq
  {n : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho, (ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered n) ⁻¹' A).indicator (fun _ => (1 : Real)) rho * wiredFkProb (hexagonal.bufferedGraph (n + 2)) (hexagonal.bufferedBoundary (n + 2)) p q rho) ≤ ∑ omega, A.indicator (fun _ => (1 : Real)) omega * wiredFkProb (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_outerBuffered_dominated n hp hp1 hq hA

/--
[triHexPlanarHexBufferedToFiniteStar_embedding_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexBufferedToFiniteStar_embedding_eq_eq
  {n : Nat}
  {v : hexagonal.BufferedVertex n} :
-- imply
  triHexPlanarFiniteStarVertexEmbedding (triHexPlanarHexBufferedOuterStarLevel n) (triHexPlanarHexBufferedToFiniteStar n v) = v.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexBufferedToFiniteStar_embedding_eq n v

/--
[triHexPlanarHexBufferedToFiniteStar_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexBufferedToFiniteStar_adjMatch_eq
  {n : Nat} :
-- imply
  ocd_AdjMatch (hexagonal.bufferedGraph n) (triHexPlanarFiniteStarGraph (triHexPlanarHexBufferedOuterStarLevel n)) (triHexPlanarHexBufferedToFiniteStar n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexBufferedToFiniteStar_adjMatch n

/--
[triHexPlanarHexBufferedToFiniteStar_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexBufferedToFiniteStar_not_boundary_eq
  {n : Nat}
  {v : hexagonal.BufferedVertex n} :
-- imply
  ¬ triHexPlanarFiniteStarBoundary (triHexPlanarHexBufferedOuterStarLevel n) (triHexPlanarHexBufferedToFiniteStar n v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexBufferedToFiniteStar_not_boundary n v

/--
[triHexPlanarHexBuffered_boundary_of_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexBuffered_boundary_of_outsideGraph_adj_eq
  {n : Nat}
  {psi : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex (triHexPlanarHexBufferedOuterStarLevel n)))}
  {x : hexagonal.BufferedVertex n}
  {c : TriHexPlanarFiniteStarVertex (triHexPlanarHexBufferedOuterStarLevel n)}
-- given
  (h : (ocd_outsideGraph (triHexPlanarFiniteStarGraph (triHexPlanarHexBufferedOuterStarLevel n)) (triHexPlanarHexBufferedToFiniteStar n) (triHexPlanarFiniteStarBoundary (triHexPlanarHexBufferedOuterStarLevel n)) psi).Adj (triHexPlanarHexBufferedToFiniteStar n x) c) :
-- imply
  hexagonal.bufferedBoundary n x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexBuffered_boundary_of_outsideGraph_adj n psi x h

/--
[triHexPlanarHexBuffered_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexBuffered_inducedWiring_le_eq
  {n : Nat}
  {psi : ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex (triHexPlanarHexBufferedOuterStarLevel n)))} :
-- imply
  ocd_inducedWiring (triHexPlanarFiniteStarGraph (triHexPlanarHexBufferedOuterStarLevel n)) (triHexPlanarHexBufferedToFiniteStar n) (triHexPlanarFiniteStarBoundary (triHexPlanarHexBufferedOuterStarLevel n)) psi ≤ boundaryCliqueGraph (hexagonal.bufferedBoundary n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexBuffered_inducedWiring_le n psi

/--
[triHexPlanarHexBuffered_outerStar_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexBuffered_outerStar_dominated_eq
  {n : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (hexagonal.BufferedVertex n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  (∑ rho, (ocd_innerRestrict (triHexPlanarHexBufferedToFiniteStar n) ⁻¹' A).indicator (fun _ => (1 : Real)) rho * wiredFkProb (triHexPlanarFiniteStarGraph (triHexPlanarHexBufferedOuterStarLevel n)) (triHexPlanarFiniteStarBoundary (triHexPlanarHexBufferedOuterStarLevel n)) p q rho) ≤ ∑ omega, A.indicator (fun _ => (1 : Real)) omega * wiredFkProb (hexagonal.bufferedGraph n) (hexagonal.bufferedBoundary n) p q omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexBuffered_outerStar_dominated n hp hp1 hq hA

/--
[triHexPlanarFiniteStarRoot_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarRoot_embedding_eq
  {n : Nat} :
-- imply
  triHexPlanarFiniteStarVertexEmbedding n (triHexPlanarFiniteStarRoot n) = triHexPlanarHexWhiteRoot := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarRoot_embedding n

/--
[triHexPlanarFiniteStarToHexBuffered_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarToHexBuffered_root_eq
  {n : Nat} :
-- imply
  triHexPlanarFiniteStarToHexBuffered n (triHexPlanarFiniteStarRoot n) = triHexPlanarHexWhiteBufferedRoot (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarToHexBuffered_root n

/--
[triHexPlanarFiniteStarToHexBuffered_cross_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarToHexBuffered_cross_boundary_eq
  {n : Nat}
  {x : TriHexPlanarFiniteStarVertex n}
  {c : hexagonal.BufferedVertex (n + 2)}
-- given
  (hadj : (hexagonal.bufferedGraph (n + 2)).Adj (triHexPlanarFiniteStarToHexBuffered n x) c)
  (hc : c ∉ Set.range (triHexPlanarFiniteStarToHexBuffered n)) :
-- imply
  triHexPlanarFiniteStarBoundary n x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarToHexBuffered_cross_boundary n x c hadj hc

/--
[triHexPlanarHexWhiteBuffered_outerEvent_subset_starRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexWhiteBuffered_outerEvent_subset_starRestrict_eq
  {n : Nat} :
-- imply
  triHexPlanarHexWhiteBufferedRootBoundaryEvent (n + 1) ⊆ ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered n) ⁻¹' triHexPlanarFiniteStarRootBoundaryEvent n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexWhiteBuffered_outerEvent_subset_starRestrict n

/--
[triHexPlanarHexBufferedToFiniteStar_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexBufferedToFiniteStar_root_eq
  {n : Nat} :
-- imply
  triHexPlanarHexBufferedToFiniteStar (n + 1) (triHexPlanarHexWhiteBufferedRoot n) = triHexPlanarFiniteStarRoot (triHexPlanarHexBufferedOuterStarLevel (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexBufferedToFiniteStar_root n

/--
[triHexPlanarHexBufferedToFiniteStar_cross_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexBufferedToFiniteStar_cross_boundary_eq
  {n : Nat}
  {x : hexagonal.BufferedVertex n}
  {c : TriHexPlanarFiniteStarVertex (triHexPlanarHexBufferedOuterStarLevel n)}
-- given
  (hadj : (triHexPlanarFiniteStarGraph (triHexPlanarHexBufferedOuterStarLevel n)).Adj (triHexPlanarHexBufferedToFiniteStar n x) c)
  (hc : c ∉ Set.range (triHexPlanarHexBufferedToFiniteStar n)) :
-- imply
  hexagonal.bufferedBoundary n x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexBufferedToFiniteStar_cross_boundary n x c hadj hc

/--
[triHexPlanarFiniteStar_outerEvent_subset_hexBufferedRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_outerEvent_subset_hexBufferedRestrict_eq
  {n : Nat} :
-- imply
  triHexPlanarFiniteStarRootBoundaryEvent (triHexPlanarHexBufferedOuterStarLevel (n + 1)) ⊆ ocd_innerRestrict (triHexPlanarHexBufferedToFiniteStar (n + 1)) ⁻¹' triHexPlanarHexWhiteBufferedRootBoundaryEvent n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_outerEvent_subset_hexBufferedRestrict n

/--
[triHexPlanarFiniteStarWiredBoundaryProbability_eq_eventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarWiredBoundaryProbability_eq_eventMass_eq
  {n : Nat}
  {p q : Real} :
-- imply
  triHexPlanarFiniteStarWiredBoundaryProbability n p q = finiteWiredEventMass (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) p q (triHexPlanarFiniteStarRootBoundaryEvent n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarWiredBoundaryProbability_eq_eventMass n

/--
[triHexPlanarHexWhiteBuffered_mass_le_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexWhiteBuffered_mass_le_star_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  finiteWiredEventMass (hexagonal.bufferedGraph (n + 2)) (hexagonal.bufferedBoundary (n + 2)) p q (triHexPlanarHexWhiteBufferedRootBoundaryEvent (n + 1)) ≤ triHexPlanarFiniteStarWiredBoundaryProbability n p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexWhiteBuffered_mass_le_star n hp hp1 hq

/--
[triHexPlanarFiniteStar_le_hexWhiteBuffered_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_le_hexWhiteBuffered_mass_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  triHexPlanarFiniteStarWiredBoundaryProbability (triHexPlanarHexBufferedOuterStarLevel (n + 1)) p q ≤ finiteWiredEventMass (hexagonal.bufferedGraph (n + 1)) (hexagonal.bufferedBoundary (n + 1)) p q (triHexPlanarHexWhiteBufferedRootBoundaryEvent n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_le_hexWhiteBuffered_mass n hp hp1 hq

/--
[triHexPlanarHexWhiteBufferedRootBoundaryEvent_eq_setBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexWhiteBufferedRootBoundaryEvent_eq_setBoundary_eq
  {n : Nat} :
-- imply
  triHexPlanarHexWhiteBufferedRootBoundaryEvent n = hexagonal.bufferedSetBoundaryEvent ({triHexPlanarHexWhiteRoot} : Set HexVertex) (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexWhiteBufferedRootBoundaryEvent_eq_setBoundary n

/--
[triHexPlanarHexWhiteBuffered_eventMass_eq_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexWhiteBuffered_eventMass_eq_measure_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  finiteWiredEventMass (hexagonal.bufferedGraph (n + 1)) (hexagonal.bufferedBoundary (n + 1)) p q (triHexPlanarHexWhiteBufferedRootBoundaryEvent n) = (hexagonal.wiredBufferedMeasure (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 HexVertex))).real (hexagonal.bufferedCylinder (n + 1) (hexagonal.bufferedSetBoundaryEvent ({triHexPlanarHexWhiteRoot} : Set HexVertex) (n + 1))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexWhiteBuffered_eventMass_eq_measure n hp hp1 hq

/--
[triHexPlanarHexWhiteBuffered_eventMass_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexWhiteBuffered_eventMass_tendsto_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => finiteWiredEventMass (hexagonal.bufferedGraph (n + 1)) (hexagonal.bufferedBoundary (n + 1)) p q (triHexPlanarHexWhiteBufferedRootBoundaryEvent n)) atTop (nhds ((hexagonal.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (hexagonal.setHitsInfinite ({triHexPlanarHexWhiteRoot} : Set HexVertex)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexWhiteBuffered_eventMass_tendsto hp hp1 hq

/--
[triHexPlanarHexStarCofinalLevel_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarHexStarCofinalLevel_tendsto_eq :
-- imply
  Tendsto (fun n => triHexPlanarHexBufferedOuterStarLevel (n + 1)) atTop atTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarHexStarCofinalLevel_tendsto

/--
[triHexPlanarFiniteStar_cofinal_tendsto_hexWhiteInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_cofinal_tendsto_hexWhiteInfinite_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => triHexPlanarFiniteStarWiredBoundaryProbability (triHexPlanarHexBufferedOuterStarLevel (n + 1)) p q) atTop (nhds ((hexagonal.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (hexagonal.setHitsInfinite ({triHexPlanarHexWhiteRoot} : Set HexVertex)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_cofinal_tendsto_hexWhiteInfinite hp hp1 hq

/--
[triHexPlanarFiniteBoundary_of_triangular_adj_not_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteBoundary_of_triangular_adj_not_terminal_eq
  {n : Nat}
  {v : TriHexPlanarFiniteTerminal n}
  {w : Site 2}
-- given
  (hvw : triangularGraph.Adj v.1 w)
  (hw : w ∉ triHexPlanarFiniteTerminalFinset n) :
-- imply
  triHexPlanarFiniteBoundary n v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteBoundary_of_triangular_adj_not_terminal n v w hvw hw

/--
[triHexPlanarFiniteTriangleToBuffered_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleToBuffered_adjMatch_eq
  {n : Nat} :
-- imply
  ocd_AdjMatch (triHexPlanarFiniteTriangleInducedGraph n) (triangular.bufferedGraph (n + 2)) (triHexPlanarFiniteTriangleToBuffered n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleToBuffered_adjMatch n

/--
[triHexPlanarFiniteTriangleToBuffered_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleToBuffered_not_boundary_eq
  {n : Nat}
  {v : TriHexPlanarFiniteTerminal n} :
-- imply
  ¬ triangular.bufferedBoundary (n + 2) (triHexPlanarFiniteTriangleToBuffered n v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleToBuffered_not_boundary n v

/--
[triHexPlanarFiniteTriangleToBuffered_cross_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleToBuffered_cross_boundary_eq
  {n : Nat}
  {v : TriHexPlanarFiniteTerminal n}
  {c : triangular.BufferedVertex (n + 2)}
-- given
  (hadj : (triangular.bufferedGraph (n + 2)).Adj (triHexPlanarFiniteTriangleToBuffered n v) c)
  (hc : c ∉ Set.range (triHexPlanarFiniteTriangleToBuffered n)) :
-- imply
  triHexPlanarFiniteBoundary n v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleToBuffered_cross_boundary n v c hadj hc

/--
[triHexPlanarFiniteTriangle_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_inducedWiring_le_eq
  {n : Nat}
  {psi : ConfigSpace (Sym2 (triangular.BufferedVertex (n + 2)))} :
-- imply
  ocd_inducedWiring (triangular.bufferedGraph (n + 2)) (triHexPlanarFiniteTriangleToBuffered n) (triangular.bufferedBoundary (n + 2)) psi ≤ boundaryCliqueGraph (triHexPlanarFiniteBoundary n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_inducedWiring_le n psi

/--
[triHexPlanarFiniteTriangle_outerBuffered_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_outerBuffered_dominated_eq
  {n : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (TriHexPlanarFiniteTerminal n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  finiteWiredEventMass (triangular.bufferedGraph (n + 2)) (triangular.bufferedBoundary (n + 2)) p q (ocd_innerRestrict (triHexPlanarFiniteTriangleToBuffered n) ⁻¹' A) ≤ finiteWiredEventMass (triHexPlanarFiniteTriangleInducedGraph n) (triHexPlanarFiniteBoundary n) p q A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_outerBuffered_dominated n hp hp1 hq hA

/--
[triHexPlanarTriBufferedToFiniteTerminal_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBufferedToFiniteTerminal_adjMatch_eq
  {n : Nat} :
-- imply
  ocd_AdjMatch (triangular.bufferedGraph n) (triHexPlanarFiniteTriangleInducedGraph (triHexPlanarTriBufferedOuterLevel n)) (triHexPlanarTriBufferedToFiniteTerminal n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBufferedToFiniteTerminal_adjMatch n

/--
[triHexPlanarTriBufferedToFiniteTerminal_not_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBufferedToFiniteTerminal_not_boundary_eq
  {n : Nat}
  {v : triangular.BufferedVertex n} :
-- imply
  ¬ triHexPlanarFiniteBoundary (triHexPlanarTriBufferedOuterLevel n) (triHexPlanarTriBufferedToFiniteTerminal n v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBufferedToFiniteTerminal_not_boundary n v

/--
[triHexPlanarTriBufferedToFiniteTerminal_cross_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBufferedToFiniteTerminal_cross_boundary_eq
  {n : Nat}
  {x : triangular.BufferedVertex n}
  {c : TriHexPlanarFiniteTerminal (triHexPlanarTriBufferedOuterLevel n)}
-- given
  (hadj : (triHexPlanarFiniteTriangleInducedGraph (triHexPlanarTriBufferedOuterLevel n)).Adj (triHexPlanarTriBufferedToFiniteTerminal n x) c)
  (hc : c ∉ Set.range (triHexPlanarTriBufferedToFiniteTerminal n)) :
-- imply
  triangular.bufferedBoundary n x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBufferedToFiniteTerminal_cross_boundary n x c hadj hc

/--
[triHexPlanarTriBuffered_boundary_of_outsideGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBuffered_boundary_of_outsideGraph_adj_eq
  {n : Nat}
  {psi : ConfigSpace (Sym2 (TriHexPlanarFiniteTerminal (triHexPlanarTriBufferedOuterLevel n)))}
  {x : triangular.BufferedVertex n}
  {c : TriHexPlanarFiniteTerminal (triHexPlanarTriBufferedOuterLevel n)}
-- given
  (h : (ocd_outsideGraph (triHexPlanarFiniteTriangleInducedGraph (triHexPlanarTriBufferedOuterLevel n)) (triHexPlanarTriBufferedToFiniteTerminal n) (triHexPlanarFiniteBoundary (triHexPlanarTriBufferedOuterLevel n)) psi).Adj (triHexPlanarTriBufferedToFiniteTerminal n x) c) :
-- imply
  triangular.bufferedBoundary n x := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBuffered_boundary_of_outsideGraph_adj n psi x h

/--
[triHexPlanarTriBuffered_inducedWiring_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBuffered_inducedWiring_le_eq
  {n : Nat}
  {psi : ConfigSpace (Sym2 (TriHexPlanarFiniteTerminal (triHexPlanarTriBufferedOuterLevel n)))} :
-- imply
  ocd_inducedWiring (triHexPlanarFiniteTriangleInducedGraph (triHexPlanarTriBufferedOuterLevel n)) (triHexPlanarTriBufferedToFiniteTerminal n) (triHexPlanarFiniteBoundary (triHexPlanarTriBufferedOuterLevel n)) psi ≤ boundaryCliqueGraph (triangular.bufferedBoundary n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBuffered_inducedWiring_le n psi

/--
[triHexPlanarTriBuffered_outerTriangle_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBuffered_outerTriangle_dominated_eq
  {n : Nat}
  {p q : Real}
  {A : Set (ConfigSpace (Sym2 (triangular.BufferedVertex n)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A) :
-- imply
  finiteWiredEventMass (triHexPlanarFiniteTriangleInducedGraph (triHexPlanarTriBufferedOuterLevel n)) (triHexPlanarFiniteBoundary (triHexPlanarTriBufferedOuterLevel n)) p q (ocd_innerRestrict (triHexPlanarTriBufferedToFiniteTerminal n) ⁻¹' A) ≤ finiteWiredEventMass (triangular.bufferedGraph n) (triangular.bufferedBoundary n) p q A := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBuffered_outerTriangle_dominated n hp hp1 hq hA

/--
[triHexPlanarFiniteTriangleRoot_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleRoot_val_eq
  {n : Nat} :
-- imply
  (triHexPlanarFiniteTriangleRoot n).1 = triHexPlanarTriRoot := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleRoot_val n

/--
[triHexPlanarFiniteTriangleToBuffered_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleToBuffered_root_eq
  {n : Nat} :
-- imply
  triHexPlanarFiniteTriangleToBuffered n (triHexPlanarFiniteTriangleRoot n) = triHexPlanarTriBufferedRoot (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleToBuffered_root n

/--
[triHexPlanarTriBufferedToFiniteTerminal_root](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBufferedToFiniteTerminal_root_eq
  {n : Nat} :
-- imply
  triHexPlanarTriBufferedToFiniteTerminal (n + 1) (triHexPlanarTriBufferedRoot n) = triHexPlanarFiniteTriangleRoot (triHexPlanarTriBufferedOuterLevel (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBufferedToFiniteTerminal_root n

/--
[triHexPlanarTriBuffered_outerEvent_subset_triangleRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBuffered_outerEvent_subset_triangleRestrict_eq
  {n : Nat} :
-- imply
  triHexPlanarTriBufferedRootBoundaryEvent (n + 1) ⊆ ocd_innerRestrict (triHexPlanarFiniteTriangleToBuffered n) ⁻¹' triHexPlanarFiniteTriangleRootBoundaryEvent n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBuffered_outerEvent_subset_triangleRestrict n

/--
[triHexPlanarFiniteTriangle_outerEvent_subset_triBufferedRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_outerEvent_subset_triBufferedRestrict_eq
  {n : Nat} :
-- imply
  triHexPlanarFiniteTriangleRootBoundaryEvent (triHexPlanarTriBufferedOuterLevel (n + 1)) ⊆ ocd_innerRestrict (triHexPlanarTriBufferedToFiniteTerminal (n + 1)) ⁻¹' triHexPlanarTriBufferedRootBoundaryEvent n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_outerEvent_subset_triBufferedRestrict n

/--
[triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eventMass_eq
  {n : Nat}
  {p q : Real} :
-- imply
  triHexPlanarFiniteTriangleInducedWiredBoundaryProbability n p q = finiteWiredEventMass (triHexPlanarFiniteTriangleInducedGraph n) (triHexPlanarFiniteBoundary n) p q (triHexPlanarFiniteTriangleRootBoundaryEvent n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eventMass n

/--
[triHexPlanarTriBuffered_mass_le_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBuffered_mass_le_triangle_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  finiteWiredEventMass (triangular.bufferedGraph (n + 2)) (triangular.bufferedBoundary (n + 2)) p q (triHexPlanarTriBufferedRootBoundaryEvent (n + 1)) ≤ triHexPlanarFiniteTriangleInducedWiredBoundaryProbability n p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBuffered_mass_le_triangle n hp hp1 hq

/--
[triHexPlanarFiniteTriangle_le_triBuffered_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_le_triBuffered_mass_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  triHexPlanarFiniteTriangleInducedWiredBoundaryProbability (triHexPlanarTriBufferedOuterLevel (n + 1)) p q ≤ finiteWiredEventMass (triangular.bufferedGraph (n + 1)) (triangular.bufferedBoundary (n + 1)) p q (triHexPlanarTriBufferedRootBoundaryEvent n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_le_triBuffered_mass n hp hp1 hq

/--
[triHexPlanarTriBufferedRootBoundaryEvent_eq_setBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBufferedRootBoundaryEvent_eq_setBoundary_eq
  {n : Nat} :
-- imply
  triHexPlanarTriBufferedRootBoundaryEvent n = triangular.bufferedSetBoundaryEvent ({triHexPlanarTriRoot} : Set (Site 2)) (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBufferedRootBoundaryEvent_eq_setBoundary n

/--
[triHexPlanarTriBuffered_eventMass_eq_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBuffered_eventMass_eq_measure_eq
  {n : Nat}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  finiteWiredEventMass (triangular.bufferedGraph (n + 1)) (triangular.bufferedBoundary (n + 1)) p q (triHexPlanarTriBufferedRootBoundaryEvent n) = (triangular.wiredBufferedMeasure (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.bufferedCylinder (n + 1) (triangular.bufferedSetBoundaryEvent ({triHexPlanarTriRoot} : Set (Site 2)) (n + 1))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBuffered_eventMass_eq_measure n hp hp1 hq

/--
[triHexPlanarTriBuffered_eventMass_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriBuffered_eventMass_tendsto_eq
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  Tendsto (fun n => finiteWiredEventMass (triangular.bufferedGraph (n + 1)) (triangular.bufferedBoundary (n + 1)) p q (triHexPlanarTriBufferedRootBoundaryEvent n)) atTop (nhds ((triangular.wiredBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.setHitsInfinite ({triHexPlanarTriRoot} : Set (Site 2))))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriBuffered_eventMass_tendsto hp hp1 hq

/--
[triHexPlanarTriCofinalLevel_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanarTriCofinalLevel_tendsto_eq :
-- imply
  Tendsto (fun n => triHexPlanarTriBufferedOuterLevel (n + 1)) atTop atTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarTriCofinalLevel_tendsto

/--
[triHexPlanar_fixedRootInfinite_real_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredCofinal.lean)
-/
@[path]
private lemma triHexPlanar_fixedRootInfinite_real_eq_eq
  {p q : Real}
-- given
  (hq : 1 ≤ q)
  (hp : p ∈ Set.Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  (hexagonal.wiredBufferedInfiniteVolume (BeffaraDC.dualParam_pos hp.1 hp.2 (zero_lt_one.trans_le hq)) (BeffaraDC.dualParam_lt_one hp.1 hp.2 (zero_lt_one.trans_le hq)) (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real (hexagonal.setHitsInfinite ({triHexPlanarHexWhiteRoot} : Set HexVertex)) = (triangular.wiredBufferedInfiniteVolume hp.1 hp.2 (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 (Site 2)))).real (triangular.setHitsInfinite ({triHexPlanarTriRoot} : Set (Site 2))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanar_fixedRootInfinite_real_eq hq hp hsurface


-- created on 2026-10-23

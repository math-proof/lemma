import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredGraphs.Part15
open Finset Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexPlanarFiniteTriangleEdge_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleEdge_val_eq
  {n : Nat}
  {a : TriHexPlanarFiniteCell n × Fin 3} :
-- imply
  Sym2.map (fun v : TriHexPlanarFiniteTerminal n => v.1) (triHexPlanarFiniteTriangleEdge n a) = triangularIndexedEdge (triHexPlanarTriangleIndexEquiv (a.1.1, a.2)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleEdge_val n a

/--
[triHexPlanarFiniteTriangleEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleEdge_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (triHexPlanarFiniteTriangleEdge n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleEdge_injective n

/--
[triHexPlanarFiniteTriangleEdge_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleEdge_ne_eq
  {n : Nat}
  {a : TriHexPlanarFiniteCell n × Fin 3} :
-- imply
  (triHexPlanarFiniteTerminalMap n a.1 (triHexTriangleEdgeTerminal1 a.2)) ≠ triHexPlanarFiniteTerminalMap n a.1 (triHexTriangleEdgeTerminal2 a.2) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleEdge_ne n a

/--
[triHexPlanarFiniteTriangleEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleEdge_mem_eq
  {n : Nat}
  {a : TriHexPlanarFiniteCell n × Fin 3} :
-- imply
  triHexPlanarFiniteTriangleEdge n a ∈ (triHexPlanarFiniteTriangleGraph n).edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleEdge_mem n a

/--
[triHexPlanarFiniteTriangleEdgeChart_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleEdgeChart_bijective_eq
  {n : Nat} :
-- imply
  Function.Bijective (triHexPlanarFiniteTriangleEdgeChart n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleEdgeChart_bijective n

/--
[triHexPlanarFiniteStarEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarEdge_injective_eq
  {n : Nat} :
-- imply
  Function.Injective (triHexPlanarFiniteStarEdge n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarEdge_injective n

/--
[triHexPlanarFiniteStarEdge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarEdge_mem_eq
  {n : Nat}
  {a : TriHexPlanarFiniteCell n × Fin 3} :
-- imply
  triHexPlanarFiniteStarEdge n a ∈ (triHexPlanarFiniteStarGraph n).edgeSet := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarEdge_mem n a

/--
[triHexPlanarFiniteStarEdgeChart_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarEdgeChart_bijective_eq
  {n : Nat} :
-- imply
  Function.Bijective (triHexPlanarFiniteStarEdgeChart n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarEdgeChart_bijective n

/--
[triHexPlanarFiniteTriangleConfigEquiv_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangleConfigEquiv_direction_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet}
  {z : TriHexPlanarFiniteCell n}
  {i : Fin 3} :
-- imply
  triHexLocalDirection (triHexPlanarFiniteTriangleConfigEquiv n omega z) i = omega (triHexPlanarFiniteTriangleEdgeEquiv n (z, i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangleConfigEquiv_direction n omega z i

/--
[triHexPlanarFiniteStarConfigEquiv_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarConfigEquiv_direction_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {z : TriHexPlanarFiniteCell n}
  {i : Fin 3} :
-- imply
  triHexLocalDirection (triHexPlanarFiniteStarConfigEquiv n omega z) i = omega (triHexPlanarFiniteStarEdgeEquiv n (z, i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarConfigEquiv_direction n omega z i

/--
[triHexPlanarFiniteTriangle_openSub_adj_cellEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_openSub_adj_cellEdge_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet}
  {z : TriHexPlanarFiniteCell n}
  {i : Fin 3}
-- given
  (hopen : triHexLocalDirection (triHexPlanarFiniteTriangleConfigEquiv n omega z) i = true) :
-- imply
  (openSub (triHexPlanarFiniteTriangleGraph n) (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Adj (triHexPlanarFiniteTerminalMap n z (triHexTriangleEdgeTerminal1 i)) (triHexPlanarFiniteTerminalMap n z (triHexTriangleEdgeTerminal2 i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_openSub_adj_cellEdge n omega z i hopen

/--
[triHexPlanarFiniteTriangle_openSub_reachable_of_connects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_openSub_reachable_of_connects_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet}
  {z : TriHexPlanarFiniteCell n}
  {i j : Fin 3}
-- given
  (hconnects : (triangleFKLocalConnectivity (triHexPlanarFiniteTriangleConfigEquiv n omega z)).Connects i j) :
-- imply
  (openSub (triHexPlanarFiniteTriangleGraph n) (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable (triHexPlanarFiniteTerminalMap n z i) (triHexPlanarFiniteTerminalMap n z j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_openSub_reachable_of_connects n omega z i j hconnects

/--
[triHexPlanarFiniteTriangle_openSub_adj_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_openSub_adj_sector_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet}
  {x y : TriHexPlanarFiniteTerminal n}
-- given
  (hxy : (openSub (triHexPlanarFiniteTriangleGraph n) (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Adj x y) :
-- imply
  (triHexPlanarFiniteTriangleSectorGraph n omega).Adj x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_openSub_adj_sector n omega hxy

/--
[triHexPlanarFiniteTriangle_sector_adj_openSub_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_sector_adj_openSub_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet}
  {x y : TriHexPlanarFiniteTerminal n}
-- given
  (hxy : (triHexPlanarFiniteTriangleSectorGraph n omega).Adj x y) :
-- imply
  (openSub (triHexPlanarFiniteTriangleGraph n) (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_sector_adj_openSub_reachable n omega hxy

/--
[triHexPlanarFiniteTriangle_openSub_reachable_iff_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_openSub_reachable_iff_sector_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet}
  {x y : TriHexPlanarFiniteTerminal n} :
-- imply
  (openSub (triHexPlanarFiniteTriangleGraph n) (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable x y ↔ (triHexPlanarFiniteTriangleSectorGraph n omega).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_openSub_reachable_iff_sector n omega x y

/--
[triHexPlanarFiniteTriangle_wired_reachable_iff_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_wired_reachable_iff_sector_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet}
  {x y : TriHexPlanarFiniteTerminal n} :
-- imply
  (wiredGraph (triHexPlanarFiniteTriangleGraph n) (triHexPlanarFiniteBoundary n) (extendActive (triHexPlanarFiniteTriangleGraph n) omega)).Reachable x y ↔ (triHexPlanarFiniteTriangleWiredSectorGraph n omega).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_wired_reachable_iff_sector n omega x y

/--
[triHexPlanarFiniteTriangle_numClustersWired_eq_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteTriangle_numClustersWired_eq_sector_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteTriangleGraph n).edgeSet} :
-- imply
  numClustersWired (triHexPlanarFiniteTriangleGraph n) (triHexPlanarFiniteBoundary n) (extendActive (triHexPlanarFiniteTriangleGraph n) omega) = Nat.card (triHexPlanarFiniteTriangleWiredSectorGraph n omega).ConnectedComponent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteTriangle_numClustersWired_eq_sector n omega

/--
[triHexPlanarFiniteStar_openSub_adj_spoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_openSub_adj_spoke_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {z : TriHexPlanarFiniteCell n}
  {i : Fin 3}
-- given
  (hopen : triHexLocalDirection (triHexPlanarFiniteStarConfigEquiv n omega z) i = true) :
-- imply
  (openSub (triHexPlanarFiniteStarGraph n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj (Sum.inl z) (Sum.inr (triHexPlanarFiniteTerminalMap n z i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_openSub_adj_spoke n omega z i hopen

/--
[triHexPlanarFiniteStar_openSub_reachable_of_connects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_openSub_reachable_of_connects_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {z : TriHexPlanarFiniteCell n}
  {i j : Fin 3}
-- given
  (hconnects : (starFKLocalConnectivity (triHexPlanarFiniteStarConfigEquiv n omega z)).Connects i j) :
-- imply
  (openSub (triHexPlanarFiniteStarGraph n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable (Sum.inr (triHexPlanarFiniteTerminalMap n z i)) (Sum.inr (triHexPlanarFiniteTerminalMap n z j)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_openSub_reachable_of_connects n omega z i j hconnects

/--
[triHexPlanarFiniteStar_openSub_adj_representative_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_openSub_adj_representative_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {u v : TriHexPlanarFiniteStarVertex n}
-- given
  (huv : (openSub (triHexPlanarFiniteStarGraph n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
-- imply
  (triHexPlanarFiniteStarSectorGraph n omega).Reachable (triHexPlanarFiniteStarRepresentative n omega u) (triHexPlanarFiniteStarRepresentative n omega v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_openSub_adj_representative_reachable n omega huv

/--
[triHexPlanarFiniteStar_sector_adj_openSub_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_sector_adj_openSub_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {x y : TriHexPlanarFiniteTerminal n}
-- given
  (hxy : (triHexPlanarFiniteStarSectorGraph n omega).Adj x y) :
-- imply
  (openSub (triHexPlanarFiniteStarGraph n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable (Sum.inr x) (Sum.inr y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_sector_adj_openSub_reachable n omega hxy

/--
[triHexPlanarFiniteStar_openSub_white_reachable_iff_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_openSub_white_reachable_iff_sector_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {x y : TriHexPlanarFiniteTerminal n} :
-- imply
  (openSub (triHexPlanarFiniteStarGraph n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable (Sum.inr x) (Sum.inr y) ↔ (triHexPlanarFiniteStarSectorGraph n omega).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_openSub_white_reachable_iff_sector n omega x y

/--
[triHexPlanarFiniteStar_wired_white_reachable_iff_sector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_wired_white_reachable_iff_sector_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {x y : TriHexPlanarFiniteTerminal n} :
-- imply
  (wiredGraph (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Reachable (Sum.inr x) (Sum.inr y) ↔ (triHexPlanarFiniteStarWiredSectorGraph n omega).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_wired_white_reachable_iff_sector n omega x y

/--
[triHexPlanarFiniteStar_openSub_adj_eq_spoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_openSub_adj_eq_spoke_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {u v : TriHexPlanarFiniteStarVertex n}
-- given
  (huv : (openSub (triHexPlanarFiniteStarGraph n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
-- imply
  ∃ z i, triHexLocalDirection (triHexPlanarFiniteStarConfigEquiv n omega z) i = true ∧ ((u = Sum.inl z ∧ v = Sum.inr (triHexPlanarFiniteTerminalMap n z i)) ∨ (v = Sum.inl z ∧ u = Sum.inr (triHexPlanarFiniteTerminalMap n z i))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_openSub_adj_eq_spoke n omega huv

/--
[triHexPlanarFiniteStar_isolatedCenter_not_wired_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_isolatedCenter_not_wired_adj_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {z : TriHexPlanarFiniteStarIsolatedCenter n omega}
  {v : TriHexPlanarFiniteStarVertex n} :
-- imply
  ¬ (wiredGraph (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj (Sum.inl z.1) v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_isolatedCenter_not_wired_adj n omega z v

/--
[triHexPlanarFiniteStar_wired_adj_representative_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_wired_adj_representative_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {u v : TriHexPlanarFiniteStarVertex n}
-- given
  (huv : (wiredGraph (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
-- imply
  (triHexPlanarFiniteStarWiredSectorGraph n omega).Reachable (triHexPlanarFiniteStarRepresentative n omega u) (triHexPlanarFiniteStarRepresentative n omega v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_wired_adj_representative_reachable n omega huv

/--
[triHexPlanarFiniteStarVertexComponentLabel_eq_of_wired_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStarVertexComponentLabel_eq_of_wired_adj_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet}
  {u v : TriHexPlanarFiniteStarVertex n}
-- given
  (huv : (wiredGraph (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) (extendActive (triHexPlanarFiniteStarGraph n) omega)).Adj u v) :
-- imply
  triHexPlanarFiniteStarVertexComponentLabel n omega u = triHexPlanarFiniteStarVertexComponentLabel n omega v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStarVertexComponentLabel_eq_of_wired_adj n omega huv

/--
[triHexPlanarFiniteStar_numClustersWired_eq_sector_add_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredGraphs.lean)
-/
@[path]
private lemma triHexPlanarFiniteStar_numClustersWired_eq_sector_add_isolated_eq
  {n : Nat}
  {omega : ConfigSpace (triHexPlanarFiniteStarGraph n).edgeSet} :
-- imply
  numClustersWired (triHexPlanarFiniteStarGraph n) (triHexPlanarFiniteStarBoundary n) (extendActive (triHexPlanarFiniteStarGraph n) omega) = Nat.card (triHexPlanarFiniteStarWiredSectorGraph n omega).ConnectedComponent + Fintype.card (TriHexPlanarFiniteStarIsolatedCenter n omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteStar_numClustersWired_eq_sector_add_isolated n omega


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15
open StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexTorusTriangleSweepEdge_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triHexTorusTriangleSweepEdge_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L}
  {i : Fin 3} :
-- imply
  ((triHexTorusTriangleSweepEdgeEquiv L (z, i) : (triangularTorusGraph L).edgeSet) : Sym2 (TorusSite L)) = s(triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i), triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusTriangleSweepEdge_val L z i

/--
[triHexTorusStarSweepEdge_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triHexTorusStarSweepEdge_val_eq
  {L : ℕ}
  [Fact (2 < L)]
  {z : TorusSite L}
  {i : Fin 3} :
-- imply
  ((triHexTorusStarSweepEdgeEquiv L (z, i) : (hexagonalTorusGraph L).edgeSet) : Sym2 (HexTorusVertex L)) = s((z, false), (triHexTorusCellTerminal L z i, true)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexTorusStarSweepEdge_val L z i

/--
[triangleFKLocalConnectivity_connects_of_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangleFKLocalConnectivity_connects_of_direction_eq
  {config : LocalConfig}
  {i : Fin 3}
-- given
  (h : triHexLocalDirection config i = true) :
-- imply
  (triangleFKLocalConnectivity config).Connects (triHexTriangleEdgeTerminal1 i) (triHexTriangleEdgeTerminal2 i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKLocalConnectivity_connects_of_direction config i h

/--
[triangularTorusActiveConfigEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorusActiveConfigEquiv_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet}
  {z : TorusSite L} :
-- imply
  triangularTorusActiveConfigEquiv L omega z = (omega (triHexTorusTriangleSweepEdgeEquiv L (z, 0)), omega (triHexTorusTriangleSweepEdgeEquiv L (z, 1)), omega (triHexTorusTriangleSweepEdgeEquiv L (z, 2))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusActiveConfigEquiv_apply L omega z

/--
[triangularTorusActiveConfigEquiv_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorusActiveConfigEquiv_direction_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet}
  {z : TorusSite L}
  {i : Fin 3} :
-- imply
  triHexLocalDirection (triangularTorusActiveConfigEquiv L omega z) i = omega (triHexTorusTriangleSweepEdgeEquiv L (z, i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusActiveConfigEquiv_direction L omega z i

/--
[hexagonalTorusActiveConfigEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorusActiveConfigEquiv_apply_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {z : TorusSite L} :
-- imply
  hexagonalTorusActiveConfigEquiv L omega z = (omega (triHexTorusStarSweepEdgeEquiv L (z, 0)), omega (triHexTorusStarSweepEdgeEquiv L (z, 1)), omega (triHexTorusStarSweepEdgeEquiv L (z, 2))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusActiveConfigEquiv_apply L omega z

/--
[hexagonalTorusActiveConfigEquiv_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorusActiveConfigEquiv_direction_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {z : TorusSite L}
  {i : Fin 3} :
-- imply
  triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega z) i = omega (triHexTorusStarSweepEdgeEquiv L (z, i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusActiveConfigEquiv_direction L omega z i

/--
[triangularTorus_openSub_adj_cellEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_openSub_adj_cellEdge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet}
  {z : TorusSite L}
  {i : Fin 3}
-- given
  (hopen : triHexLocalDirection (triangularTorusActiveConfigEquiv L omega z) i = true) :
-- imply
  (openSub (triangularTorusGraph L) (extendActive (triangularTorusGraph L) omega)).Adj (triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal1 i)) (triHexTorusCellTerminal L z (triHexTriangleEdgeTerminal2 i)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_openSub_adj_cellEdge L omega z i hopen

/--
[hexagonalTorus_openSub_adj_spoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_openSub_adj_spoke_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {z : TorusSite L}
  {i : Fin 3}
-- given
  (hopen : triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega z) i = true) :
-- imply
  (openSub (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega)).Adj (z, false) (triHexTorusCellTerminal L z i, true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_openSub_adj_spoke L omega z i hopen

/--
[hexagonalTorus_openSub_adj_center_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_openSub_adj_center_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {z : TorusSite L}
  {v : HexTorusVertex L} :
-- imply
  (openSub (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega)).Adj (z, false) v ↔ ∃ i : Fin 3, triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega z) i = true ∧ v = (triHexTorusCellTerminal L z i, true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_openSub_adj_center_iff L omega z v

/--
[triangleFKLocalConnectivity_connects_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangleFKLocalConnectivity_connects_zero_one_eq
  {config : LocalConfig} :
-- imply
  (triangleFKLocalConnectivity config).Connects 0 1 ↔ triHexLocalDirection config 2 = true ∨ (triHexLocalDirection config 0 = true ∧ triHexLocalDirection config 1 = true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKLocalConnectivity_connects_zero_one config

/--
[triangleFKLocalConnectivity_connects_zero_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangleFKLocalConnectivity_connects_zero_two_eq
  {config : LocalConfig} :
-- imply
  (triangleFKLocalConnectivity config).Connects 0 2 ↔ triHexLocalDirection config 1 = true ∨ (triHexLocalDirection config 0 = true ∧ triHexLocalDirection config 2 = true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKLocalConnectivity_connects_zero_two config

/--
[triangleFKLocalConnectivity_connects_one_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangleFKLocalConnectivity_connects_one_two_eq
  {config : LocalConfig} :
-- imply
  (triangleFKLocalConnectivity config).Connects 1 2 ↔ triHexLocalDirection config 0 = true ∨ (triHexLocalDirection config 1 = true ∧ triHexLocalDirection config 2 = true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKLocalConnectivity_connects_one_two config

/--
[triangularTorus_openSub_reachable_of_connects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_openSub_reachable_of_connects_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet}
  {z : TorusSite L}
  {i j : Fin 3}
-- given
  (hconnects : (triangleFKLocalConnectivity (triangularTorusActiveConfigEquiv L omega z)).Connects i j) :
-- imply
  (openSub (triangularTorusGraph L) (extendActive (triangularTorusGraph L) omega)).Reachable (triHexTorusCellTerminal L z i) (triHexTorusCellTerminal L z j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_openSub_reachable_of_connects L omega z i j hconnects

/--
[triangularTorus_openSub_adj_terminalSectorGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_openSub_adj_terminalSectorGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet}
  {x y : TorusSite L}
-- given
  (hxy : (openSub (triangularTorusGraph L) (extendActive (triangularTorusGraph L) omega)).Adj x y) :
-- imply
  (triangularTorusTerminalSectorGraph L omega).Adj x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_openSub_adj_terminalSectorGraph L omega hxy

/--
[triangularTorus_terminalSectorGraph_adj_openSub_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_terminalSectorGraph_adj_openSub_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet}
  {x y : TorusSite L}
-- given
  (hxy : (triangularTorusTerminalSectorGraph L omega).Adj x y) :
-- imply
  (openSub (triangularTorusGraph L) (extendActive (triangularTorusGraph L) omega)).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_terminalSectorGraph_adj_openSub_reachable L omega hxy

/--
[triangularTorus_openSub_reachable_iff_terminalSectorGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_openSub_reachable_iff_terminalSectorGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet}
  {x y : TorusSite L} :
-- imply
  (openSub (triangularTorusGraph L) (extendActive (triangularTorusGraph L) omega)).Reachable x y ↔ (triangularTorusTerminalSectorGraph L omega).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_openSub_reachable_iff_terminalSectorGraph L omega x y

/--
[reachable_map_of_adj_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma reachable_map_of_adj_reachable_eq
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {f : V → W}
  {x y : V}
-- given
  (hedge : ∀ x y, G.Adj x y → H.Reachable (f x) (f y))
  (hxy : G.Reachable x y) :
-- imply
  H.Reachable (f x) (f y) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.reachable_map_of_adj_reachable G H f hedge hxy

/--
[triangularTorus_numClusters_eq_terminalSector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_numClusters_eq_terminalSector_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet} :
-- imply
  numClusters (triangularTorusGraph L) (extendActive (triangularTorusGraph L) omega) = Fintype.card (triangularTorusTerminalSectorGraph L omega).ConnectedComponent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_numClusters_eq_terminalSector L omega

/--
[starFKLocalConnectivity_connects_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma starFKLocalConnectivity_connects_iff_eq
  {config : LocalConfig}
  {i j : Fin 3} :
-- imply
  (starFKLocalConnectivity config).Connects i j ↔ i = j ∨ (triHexLocalDirection config i = true ∧ triHexLocalDirection config j = true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKLocalConnectivity_connects_iff config i j

/--
[hexagonalTorus_openSub_reachable_of_connects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_openSub_reachable_of_connects_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {z : TorusSite L}
  {i j : Fin 3}
-- given
  (hconnects : (starFKLocalConnectivity (hexagonalTorusActiveConfigEquiv L omega z)).Connects i j) :
-- imply
  (openSub (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega)).Reachable (triHexTorusCellTerminal L z i, true) (triHexTorusCellTerminal L z j, true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_openSub_reachable_of_connects L omega z i j hconnects

/--
[triHexFKTerminalSectorGraph_reachable_of_connects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triHexFKTerminalSectorGraph_reachable_of_connects_eq
  [Fintype I]
  [DecidableEq I]
  [DecidableEq V]
  {terminal : I → Fin 3 → V}
  {sector : I → ThreeTerminalConnectivity}
  {cell : I}
  {i j : Fin 3}
-- given
  (hconnects : (sector cell).Connects i j) :
-- imply
  (triHexFKTerminalSectorGraph terminal sector).Reachable (terminal cell i) (terminal cell j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFKTerminalSectorGraph_reachable_of_connects terminal sector cell i j hconnects

/--
[starFKRepresentativeDirection_open_of_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma starFKRepresentativeDirection_open_of_open_eq
  {config : LocalConfig}
  {i : Fin 3}
-- given
  (hi : triHexLocalDirection config i = true) :
-- imply
  triHexLocalDirection config (starFKRepresentativeDirection config) = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKRepresentativeDirection_open_of_open config i hi

/--
[hexagonalTorus_openSub_adj_representative_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_openSub_adj_representative_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {u v : HexTorusVertex L}
-- given
  (huv : (openSub (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega)).Adj u v) :
-- imply
  (hexagonalTorusTerminalSectorGraph L omega).Reachable (hexagonalTorusOpenRepresentative L omega u) (hexagonalTorusOpenRepresentative L omega v) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_openSub_adj_representative_reachable L omega huv

/--
[hexagonalTorus_terminalSectorGraph_adj_openSub_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_terminalSectorGraph_adj_openSub_reachable_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {x y : TorusSite L}
-- given
  (hxy : (hexagonalTorusTerminalSectorGraph L omega).Adj x y) :
-- imply
  (openSub (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega)).Reachable (x, true) (y, true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_terminalSectorGraph_adj_openSub_reachable L omega hxy

/--
[hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {x y : TorusSite L} :
-- imply
  (openSub (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega)).Reachable (x, true) (y, true) ↔ (hexagonalTorusTerminalSectorGraph L omega).Reachable x y := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph L omega x y

/--
[hexagonalTorus_openSub_adj_eq_spoke](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_openSub_adj_eq_spoke_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {u v : HexTorusVertex L}
-- given
  (huv : (openSub (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega)).Adj u v) :
-- imply
  ∃ z i, triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega z) i = true ∧ ((u = (z, false) ∧ v = (triHexTorusCellTerminal L z i, true)) ∨ (v = (z, false) ∧ u = (triHexTorusCellTerminal L z i, true))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_openSub_adj_eq_spoke L omega huv

/--
[starFKRepresentativeDirection_open_of_not_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma starFKRepresentativeDirection_open_of_not_closed_eq
  {config : LocalConfig}
-- given
  (h : config ≠ (false, false, false)) :
-- imply
  triHexLocalDirection config (starFKRepresentativeDirection config) = true := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKRepresentativeDirection_open_of_not_closed config h

/--
[hexagonalTorus_isolatedCenter_not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_isolatedCenter_not_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {z : HexagonalTorusIsolatedCenter L omega}
  {v : HexTorusVertex L} :
-- imply
  ¬ (openSub (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega)).Adj (z.1, false) v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_isolatedCenter_not_adj L omega z v

/--
[hexagonalTorusVertexComponentLabel_eq_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorusVertexComponentLabel_eq_of_adj_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
  {u v : HexTorusVertex L}
-- given
  (huv : (openSub (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega)).Adj u v) :
-- imply
  hexagonalTorusVertexComponentLabel L omega u = hexagonalTorusVertexComponentLabel L omega v := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusVertexComponentLabel_eq_of_adj L omega huv

/--
[hexagonalTorus_numClusters_eq_terminalSector_add_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_numClusters_eq_terminalSector_add_isolated_eq
  {L : ℕ}
  [Fact (2 < L)]
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet} :
-- imply
  numClusters (hexagonalTorusGraph L) (extendActive (hexagonalTorusGraph L) omega) = Fintype.card (hexagonalTorusTerminalSectorGraph L omega).ConnectedComponent + Fintype.card (HexagonalTorusIsolatedCenter L omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_numClusters_eq_terminalSector_add_isolated L omega

/--
[edgeProductW_extendActive_eq_activeProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma edgeProductW_extendActive_eq_activeProduct_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {omega : ConfigSpace G.edgeSet} :
-- imply
  edgeProductW G pf (extendActive G omega) = ∏ e : G.edgeSet, if omega e then pf e.1 else 1 - pf e.1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.edgeProductW_extendActive_eq_activeProduct G pf omega

/--
[edgeProductW_extendActive_odds_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma edgeProductW_extendActive_odds_factor_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {pf : Sym2 V → ℝ}
  {odds : G.edgeSet → ℝ}
  {omega : ConfigSpace G.edgeSet}
-- given
  (h : ∀ e : G.edgeSet, pf e.1 = (1 - pf e.1) * odds e) :
-- imply
  edgeProductW G pf (extendActive G omega) = (∏ e : G.edgeSet, (1 - pf e.1)) * ∏ e : G.edgeSet, if omega e then odds e else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.edgeProductW_extendActive_odds_factor G pf odds h omega

/--
[triangleFKLocalOddsWeight_eq_directionProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangleFKLocalOddsWeight_eq_directionProduct_eq
  {y0 y1 y2 : ℝ}
  {config : LocalConfig} :
-- imply
  triangleFKLocalOddsWeight y0 y1 y2 config = ∏ i : Fin 3, if triHexLocalDirection config i then triHexDirectionOdds y0 y1 y2 i else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKLocalOddsWeight_eq_directionProduct y0 y1 y2 config

/--
[starFKLocalOddsWeight_eq_isolated_mul_directionProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma starFKLocalOddsWeight_eq_isolated_mul_directionProduct_eq
  {q y0 y1 y2 : ℝ}
  {config : LocalConfig} :
-- imply
  starFKLocalOddsWeight q y0 y1 y2 config = starFKIsolatedCenterFactor q config * ∏ i : Fin 3, if triHexLocalDirection config i then triHexDirectionOdds y0 y1 y2 i else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKLocalOddsWeight_eq_isolated_mul_directionProduct q y0 y1 y2 config

/--
[triangleFKGlobalLocalOdds_eq_directionProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangleFKGlobalLocalOdds_eq_directionProduct_eq
  [Fintype I]
  {y0 y1 y2 : ℝ}
  {config : I → LocalConfig} :
-- imply
  (∏ z, triangleFKLocalOddsWeight y0 y1 y2 (config z)) = ∏ a : I × Fin 3, if triHexLocalDirection (config a.1) a.2 then triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangleFKGlobalLocalOdds_eq_directionProduct y0 y1 y2 config

/--
[starFKGlobalLocalOdds_eq_isolated_mul_directionProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma starFKGlobalLocalOdds_eq_isolated_mul_directionProduct_eq
  [Fintype I]
  {q y0 y1 y2 : ℝ}
  {config : I → LocalConfig} :
-- imply
  (∏ z, starFKLocalOddsWeight q y0 y1 y2 (config z)) = (∏ z, starFKIsolatedCenterFactor q (config z)) * ∏ a : I × Fin 3, if triHexLocalDirection (config a.1) a.2 then triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.starFKGlobalLocalOdds_eq_isolated_mul_directionProduct q y0 y1 y2 config

/--
[triangularTorus_localOddsProduct_eq_activeOddsProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_localOddsProduct_eq_activeOddsProduct_eq
  {L : ℕ}
  [Fact (2 < L)]
  {y0 y1 y2 : ℝ}
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet} :
-- imply
  (∏ z, triangleFKLocalOddsWeight y0 y1 y2 (triangularTorusActiveConfigEquiv L omega z)) = ∏ e : (triangularTorusGraph L).edgeSet, if omega e then triangularTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_localOddsProduct_eq_activeOddsProduct L y0 y1 y2 omega

/--
[hexagonalTorus_localOddsProduct_eq_activeOddsProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_localOddsProduct_eq_activeOddsProduct_eq
  {L : ℕ}
  [Fact (2 < L)]
  {q y0 y1 y2 : ℝ}
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet} :
-- imply
  (∏ z, starFKLocalOddsWeight q y0 y1 y2 (hexagonalTorusActiveConfigEquiv L omega z)) = (∏ z, starFKIsolatedCenterFactor q (hexagonalTorusActiveConfigEquiv L omega z)) * ∏ e : (hexagonalTorusGraph L).edgeSet, if omega e then hexagonalTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_localOddsProduct_eq_activeOddsProduct L q y0 y1 y2 omega

/--
[fintype_prod_ite_eq_pow_card_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma fintype_prod_ite_eq_pow_card_subtype_eq
  [Fintype I]
  [DecidablePred P]
  [Fintype {i // P i}]
  {q : ℝ}
-- given
  (P : I → Prop) :
-- imply
  (∏ i, if P i then q else 1) = q ^ Fintype.card {i // P i} := by
-- proof
  apply StatMech.FK.PeriodicPlanar.fintype_prod_ite_eq_pow_card_subtype P q

/--
[hexagonalTorus_isolatedCenterFactor_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_isolatedCenterFactor_product_eq
  {L : ℕ}
  [Fact (2 < L)]
  {q : ℝ}
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet} :
-- imply
  (∏ z, starFKIsolatedCenterFactor q (hexagonalTorusActiveConfigEquiv L omega z)) = q ^ Fintype.card (HexagonalTorusIsolatedCenter L omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_isolatedCenterFactor_product L q omega

/--
[triangularTorus_activeWeight_eq_closedProduct_mul_cellWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_activeWeight_eq_closedProduct_mul_cellWeight_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pf : Sym2 (TorusSite L) → ℝ}
  {q y0 y1 y2 : ℝ}
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet}
-- given
  (hodds : ∀ e : (triangularTorusGraph L).edgeSet, pf e.1 = (1 - pf e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e) :
-- imply
  activeWeight (triangularTorusGraph L) pf q omega = (∏ e : (triangularTorusGraph L).edgeSet, (1 - pf e.1)) * (triHexTorusSectorClusterWeight L q (fun z => triangleFKLocalConnectivity (triangularTorusActiveConfigEquiv L omega z)) * ∏ z, triangleFKLocalOddsWeight y0 y1 y2 (triangularTorusActiveConfigEquiv L omega z)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_activeWeight_eq_closedProduct_mul_cellWeight L pf q y0 y1 y2 hodds omega

/--
[hexagonalTorus_activeWeight_eq_closedProduct_mul_cellWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_activeWeight_eq_closedProduct_mul_cellWeight_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pf : Sym2 (HexTorusVertex L) → ℝ}
  {q y0 y1 y2 : ℝ}
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet}
-- given
  (hodds : ∀ e : (hexagonalTorusGraph L).edgeSet, pf e.1 = (1 - pf e.1) * hexagonalTorusSweepEdgeOdds L y0 y1 y2 e) :
-- imply
  activeWeight (hexagonalTorusGraph L) pf q omega = (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pf e.1)) * (triHexTorusSectorClusterWeight L q (fun z => starFKLocalConnectivity (hexagonalTorusActiveConfigEquiv L omega z)) * ∏ z, starFKLocalOddsWeight q y0 y1 y2 (hexagonalTorusActiveConfigEquiv L omega z)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_activeWeight_eq_closedProduct_mul_cellWeight L pf q y0 y1 y2 hodds omega

/--
[triangularTorus_activeZ_eq_closedProduct_mul_globalConfigSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_activeZ_eq_closedProduct_mul_globalConfigSum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pf : Sym2 (TorusSite L) → ℝ}
  {q y0 y1 y2 : ℝ}
-- given
  (hodds : ∀ e : (triangularTorusGraph L).edgeSet, pf e.1 = (1 - pf e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e) :
-- imply
  activeZ (triangularTorusGraph L) pf q = (∏ e : (triangularTorusGraph L).edgeSet, (1 - pf e.1)) * triangleFKGlobalConfigSum y0 y1 y2 (triHexTorusSectorClusterWeight L q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_activeZ_eq_closedProduct_mul_globalConfigSum L pf q y0 y1 y2 hodds

/--
[hexagonalTorus_activeZ_eq_closedProduct_mul_globalConfigSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_activeZ_eq_closedProduct_mul_globalConfigSum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pf : Sym2 (HexTorusVertex L) → ℝ}
  {q y0 y1 y2 : ℝ}
-- given
  (hodds : ∀ e : (hexagonalTorusGraph L).edgeSet, pf e.1 = (1 - pf e.1) * hexagonalTorusSweepEdgeOdds L y0 y1 y2 e) :
-- imply
  activeZ (hexagonalTorusGraph L) pf q = (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pf e.1)) * starFKGlobalConfigSum q y0 y1 y2 (triHexTorusSectorClusterWeight L q) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_activeZ_eq_closedProduct_mul_globalConfigSum L pf q y0 y1 y2 hodds

/--
[triHexFK_globalConfigSum_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triHexFK_globalConfigSum_identity_eq
  [Fintype I]
  [DecidableEq I]
  {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
  {external : (I → ThreeTerminalConnectivity) → ℝ}
-- given
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  (y0 * y1 * y2) ^ Fintype.card I * starFKGlobalConfigSum q y0Star y1Star y2Star external = (q ^ 2) ^ Fintype.card I * triangleFKGlobalConfigSum y0 y1 y2 external := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_globalConfigSum_identity h0 h1 h2 hsurface external

/--
[triHexFK_torus_activeZ_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triHexFK_torus_activeZ_identity_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pfTri : Sym2 (TorusSite L) → ℝ}
  {pfStar : Sym2 (HexTorusVertex L) → ℝ}
  {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
-- given
  (hoddsTri : ∀ e : (triangularTorusGraph L).edgeSet, pfTri e.1 = (1 - pfTri e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e)
  (hoddsStar : ∀ e : (hexagonalTorusGraph L).edgeSet, pfStar e.1 = (1 - pfStar e.1) * hexagonalTorusSweepEdgeOdds L y0Star y1Star y2Star e)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  (y0 * y1 * y2) ^ Fintype.card (TorusSite L) * (∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) * activeZ (hexagonalTorusGraph L) pfStar q = (q ^ 2) ^ Fintype.card (TorusSite L) * (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1)) * activeZ (triangularTorusGraph L) pfTri q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_torus_activeZ_identity L pfTri pfStar hoddsTri hoddsStar h0 h1 h2 hsurface

/--
[triangularTorus_activeNumer_sector_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorus_activeNumer_sector_eq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pf : Sym2 (TorusSite L) → ℝ}
  {q y0 y1 y2 : ℝ}
  {observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ}
-- given
  (hodds : ∀ e : (triangularTorusGraph L).edgeSet, pf e.1 = (1 - pf e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e) :
-- imply
  activeNumer (triangularTorusGraph L) pf q (triangularTorusSectorObservable L observable) = (∏ e : (triangularTorusGraph L).edgeSet, (1 - pf e.1)) * triangleFKGlobalConfigSum y0 y1 y2 (fun sector => triHexTorusSectorClusterWeight L q sector * observable sector) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorus_activeNumer_sector_eq L pf q y0 y1 y2 hodds observable

/--
[hexagonalTorus_activeNumer_sector_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorus_activeNumer_sector_eq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pf : Sym2 (HexTorusVertex L) → ℝ}
  {q y0 y1 y2 : ℝ}
  {observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ}
-- given
  (hodds : ∀ e : (hexagonalTorusGraph L).edgeSet, pf e.1 = (1 - pf e.1) * hexagonalTorusSweepEdgeOdds L y0 y1 y2 e) :
-- imply
  activeNumer (hexagonalTorusGraph L) pf q (hexagonalTorusSectorObservable L observable) = (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pf e.1)) * starFKGlobalConfigSum q y0 y1 y2 (fun sector => triHexTorusSectorClusterWeight L q sector * observable sector) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorus_activeNumer_sector_eq L pf q y0 y1 y2 hodds observable

/--
[triHexFK_torus_activeSectorRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triHexFK_torus_activeSectorRatio_eq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pfTri : Sym2 (TorusSite L) → ℝ}
  {pfStar : Sym2 (HexTorusVertex L) → ℝ}
  {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
  {observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ}
-- given
  (hq : q ≠ 0)
  (hyprod : y0 * y1 * y2 ≠ 0)
  (hpfTri : ∀ e : (triangularTorusGraph L).edgeSet, pfTri e.1 ≠ 1)
  (hpfStar : ∀ e : (hexagonalTorusGraph L).edgeSet, pfStar e.1 ≠ 1)
  (hoddsTri : ∀ e : (triangularTorusGraph L).edgeSet, pfTri e.1 = (1 - pfTri e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e)
  (hoddsStar : ∀ e : (hexagonalTorusGraph L).edgeSet, pfStar e.1 = (1 - pfStar e.1) * hexagonalTorusSweepEdgeOdds L y0Star y1Star y2Star e)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  activeNumer (hexagonalTorusGraph L) pfStar q (hexagonalTorusSectorObservable L observable) / activeZ (hexagonalTorusGraph L) pfStar q = activeNumer (triangularTorusGraph L) pfTri q (triangularTorusSectorObservable L observable) / activeZ (triangularTorusGraph L) pfTri q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_torus_activeSectorRatio_eq L pfTri pfStar hq hyprod hpfTri hpfStar hoddsTri hoddsStar h0 h1 h2 hsurface observable

/--
[triangularTorusSectorTwoPointObservable_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triangularTorusSectorTwoPointObservable_eq_indicator_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : TorusSite L}
  {omega : ConfigSpace (triangularTorusGraph L).edgeSet} :
-- imply
  triangularTorusSectorObservable L (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) omega = triangularTorusActiveTwoPointIndicator L x y omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularTorusSectorTwoPointObservable_eq_indicator L x y omega

/--
[hexagonalTorusSectorTwoPointObservable_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma hexagonalTorusSectorTwoPointObservable_eq_indicator_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x y : TorusSite L}
  {omega : ConfigSpace (hexagonalTorusGraph L).edgeSet} :
-- imply
  hexagonalTorusSectorObservable L (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) omega = hexagonalTorusActiveWhiteTwoPointIndicator L x y omega := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalTorusSectorTwoPointObservable_eq_indicator L x y omega

/--
[triHexFK_torus_activeTwoPointRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean)
-/
@[path]
private lemma triHexFK_torus_activeTwoPointRatio_eq_eq
  {L : ℕ}
  [Fact (2 < L)]
  {pfTri : Sym2 (TorusSite L) → ℝ}
  {pfStar : Sym2 (HexTorusVertex L) → ℝ}
  {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
  {x y : TorusSite L}
-- given
  (hq : q ≠ 0)
  (hyprod : y0 * y1 * y2 ≠ 0)
  (hpfTri : ∀ e : (triangularTorusGraph L).edgeSet, pfTri e.1 ≠ 1)
  (hpfStar : ∀ e : (hexagonalTorusGraph L).edgeSet, pfStar e.1 ≠ 1)
  (hoddsTri : ∀ e : (triangularTorusGraph L).edgeSet, pfTri e.1 = (1 - pfTri e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e)
  (hoddsStar : ∀ e : (hexagonalTorusGraph L).edgeSet, pfStar e.1 = (1 - pfStar e.1) * hexagonalTorusSweepEdgeOdds L y0Star y1Star y2Star e)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
-- imply
  activeNumer (hexagonalTorusGraph L) pfStar q (hexagonalTorusActiveWhiteTwoPointIndicator L x y) / activeZ (hexagonalTorusGraph L) pfStar q = activeNumer (triangularTorusGraph L) pfTri q (triangularTorusActiveTwoPointIndicator L x y) / activeZ (triangularTorusGraph L) pfTri q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_torus_activeTwoPointRatio_eq L pfTri pfStar hq hyprod hpfTri hpfStar hoddsTri hoddsStar h0 h1 h2 hsurface x y


-- created on 2026-10-23

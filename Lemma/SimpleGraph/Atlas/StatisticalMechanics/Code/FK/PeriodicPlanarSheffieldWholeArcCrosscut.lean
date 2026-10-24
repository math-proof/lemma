import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldWholeArcCrosscut
open Set SimpleGraph Topology StatMech StatMech.Lattice StatMech.ContinuousHalfPlaneCrosscut StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[jec_rayCount_halfPlaneReturnPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma jec_rayCount_halfPlaneReturnPath_eq
  {alpha c d e : Int}
-- given
  (hcd : c <= d)
  (hce : c < e)
  (hed : e < d) :
-- imply
  jec_rayCount ![alpha, e] (halfPlaneReturnPath alpha c d hcd) = 1 := by
-- proof
  apply StatMech.Lattice.jec_rayCount_halfPlaneReturnPath alpha c d e hcd hce hed

/--
[mem_halfPlaneReturnPath_of_coord_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma mem_halfPlaneReturnPath_of_coord_ge_eq
  {alpha c d : Int}
  {z : Site 2}
-- given
  (hcd : c <= d)
  (hz : z ∈ (halfPlaneReturnPath alpha c d hcd).support)
  (hz0 : alpha <= z 0) :
-- imply
  z = ![alpha, d] ∨ z = ![alpha, c] := by
-- proof
  apply StatMech.Lattice.mem_halfPlaneReturnPath_of_coord_ge alpha c d hcd hz hz0

/--
[halfPlaneReturnPath_coord_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma halfPlaneReturnPath_coord_le_eq
  {alpha c d : Int}
  {z : Site 2}
-- given
  (hcd : c <= d)
  (hz : z ∈ (halfPlaneReturnPath alpha c d hcd).support) :
-- imply
  z 0 <= alpha := by
-- proof
  apply StatMech.Lattice.halfPlaneReturnPath_coord_le alpha c d hcd hz

/--
[halfPlaneReturnPath_vertical_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma halfPlaneReturnPath_vertical_bounds_eq
  {alpha c d : Int}
  {z : Site 2}
-- given
  (hcd : c <= d)
  (hz : z ∈ (halfPlaneReturnPath alpha c d hcd).support) :
-- imply
  c <= z 1 ∧ z 1 <= d := by
-- proof
  apply StatMech.Lattice.halfPlaneReturnPath_vertical_bounds alpha c d hcd hz

/--
[jec_rayCount_eq_zero_of_support_below](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma jec_rayCount_eq_zero_of_support_below_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : ∀ p ∈ w.support, p 1 < z 1) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Lattice.jec_rayCount_eq_zero_of_support_below z w h

/--
[jec_rayCount_eq_zero_of_support_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma jec_rayCount_eq_zero_of_support_above_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : ∀ p ∈ w.support, z 1 < p 1) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Lattice.jec_rayCount_eq_zero_of_support_above z w h

/--
[jec_rayParity_eq_along_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma jec_rayParity_eq_along_walk_eq
  {a x y : Site 2}
  {loop : (hypercubicLattice 2).Walk a a}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hdisj : ∀ z, z ∈ p.support -> z ∉ loop.support) :
-- imply
  (Even (jec_rayCount x loop) <-> Even (jec_rayCount y loop)) := by
-- proof
  apply StatMech.Lattice.jec_rayParity_eq_along_walk loop p hdisj

/--
[halfPlane_walks_intersect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma halfPlane_walks_intersect_eq
  {alpha c d e beta f : Int}
  {crosscut : (hypercubicLattice 2).Walk ![alpha, c] ![alpha, d]}
  {escape : (hypercubicLattice 2).Walk ![alpha, e] ![beta, f]}
-- given
  (hce : c < e)
  (hed : e < d)
  (hcrossLeft : ∀ z, z ∈ crosscut.support -> alpha <= z 0)
  (hcrossRight : ∀ z, z ∈ crosscut.support -> z 0 < beta)
  (hescapeLeft : ∀ z, z ∈ escape.support -> alpha <= z 0) :
-- imply
  ∃ z, z ∈ crosscut.support ∧ z ∈ escape.support := by
-- proof
  apply StatMech.Lattice.halfPlane_walks_intersect alpha c d e beta f hce hed crosscut escape hcrossLeft hcrossRight hescapeLeft

/--
[halfPlane_walks_intersect_of_endpoint_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma halfPlane_walks_intersect_of_endpoint_outside_eq
  {alpha c d e beta f : Int}
  {crosscut : (hypercubicLattice 2).Walk ![alpha, c] ![alpha, d]}
  {escape : (hypercubicLattice 2).Walk ![alpha, e] ![beta, f]}
-- given
  (hce : c < e)
  (hed : e < d)
  (hcrossLeft : ∀ z, z ∈ crosscut.support -> alpha <= z 0)
  (hescapeLeft : ∀ z, z ∈ escape.support -> alpha <= z 0)
  (houtside : (∀ z, z ∈ crosscut.support -> z 0 < beta) ∨ (∀ z, z ∈ crosscut.support -> z 1 < f) ∨ (∀ z, z ∈ crosscut.support -> f < z 1)) :
-- imply
  ∃ z, z ∈ crosscut.support ∧ z ∈ escape.support := by
-- proof
  apply StatMech.Lattice.halfPlane_walks_intersect_of_endpoint_outside alpha c d e beta f hce hed crosscut escape hcrossLeft hescapeLeft houtside

/--
[gridConnector_coord_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma gridConnector_coord_ge_eq
  {alpha : Int}
  {x y z : Site 2}
-- given
  (hx : alpha <= x 0)
  (hy : alpha <= y 0)
  (hz : z ∈ (gridConnector x y).support) :
-- imply
  alpha <= z 0 := by
-- proof
  apply StatMech.ContinuousHalfPlaneCrosscut.gridConnector_coord_ge hx hy hz

/--
[gridWalk_coord_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma gridWalk_coord_ge_eq
  {alpha : Int}
  {g : Nat -> Site 2}
  {N : Nat}
  {z : Site 2}
-- given
  (hg : ∀ k, k <= N -> alpha <= g k 0)
  (hz : z ∈ (gridWalk g N).support) :
-- imply
  alpha <= z 0 := by
-- proof
  apply StatMech.ContinuousHalfPlaneCrosscut.gridWalk_coord_ge hg hz

/--
[sampledGrid_walk_coord_ge_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma sampledGrid_walk_coord_ge_source_eq
  {p q : Fin 2 -> Real}
  {gamma : Path p q}
  {n N : Nat}
  {z : Site 2}
-- given
  (hgamma : ∀ t : unitInterval, p 0 <= gamma t 0)
  (hN : 0 < N)
  (hz : z ∈ (gridWalk (sampledGrid n N hN gamma) N).support) :
-- imply
  gridFloor n p 0 <= z 0 := by
-- proof
  apply StatMech.ContinuousHalfPlaneCrosscut.sampledGrid_walk_coord_ge_source gamma hgamma hN hz

/--
[gridFloor_coord_lt_of_two_mesh_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma gridFloor_coord_lt_of_two_mesh_lt_eq
  {n : Nat}
  {p q : Fin 2 -> Real}
  {i : Fin 2}
-- given
  (hn : 0 < n)
  (hgap : 2 / (n : Real) < q i - p i) :
-- imply
  gridFloor n p i < gridFloor n q i := by
-- proof
  apply StatMech.ContinuousHalfPlaneCrosscut.gridFloor_coord_lt_of_two_mesh_lt hn hgap

/--
[wholeArc_intersects_escape_of_margin_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma wholeArc_intersects_escape_of_margin_outside_eq
  {lo hi root far : Fin 2 -> Real}
  {crosscut : Path lo hi}
  {escape : Path root far}
  {margin : Real}
-- given
  (hloRootX : lo 0 = root 0)
  (hhiRootX : hi 0 = root 0)
  (hloRootY : lo 1 < root 1)
  (hrootHiY : root 1 < hi 1)
  (hcrossLeft : ∀ t : unitInterval, lo 0 <= crosscut t 0)
  (hescapeLeft : ∀ t : unitInterval, root 0 <= escape t 0)
  (hmargin : 0 < margin)
  (houtside : (∀ t : unitInterval, crosscut t 0 + margin < far 0) ∨ (∀ t : unitInterval, crosscut t 1 + margin < far 1) ∨ (∀ t : unitInterval, far 1 + margin < crosscut t 1)) :
-- imply
  ∃ t s : unitInterval, crosscut t = escape s := by
-- proof
  apply StatMech.ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape_of_margin_outside crosscut escape hloRootX hhiRootX hloRootY hrootHiY hcrossLeft hescapeLeft hmargin houtside

/--
[wholeArc_intersects_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma wholeArc_intersects_escape_eq
  {lo hi root far : Fin 2 -> Real}
  {crosscut : Path lo hi}
  {escape : Path root far}
  {margin : Real}
-- given
  (hloRootX : lo 0 = root 0)
  (hhiRootX : hi 0 = root 0)
  (hloRootY : lo 1 < root 1)
  (hrootHiY : root 1 < hi 1)
  (hcrossLeft : ∀ t : unitInterval, lo 0 <= crosscut t 0)
  (hescapeLeft : ∀ t : unitInterval, root 0 <= escape t 0)
  (hmargin : 0 < margin)
  (hfar : ∀ t : unitInterval, crosscut t 0 + margin < far 0) :
-- imply
  ∃ t s : unitInterval, crosscut t = escape s := by
-- proof
  apply StatMech.ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape crosscut escape hloRootX hhiRootX hloRootY hrootHiY hcrossLeft hescapeLeft hmargin hfar

/--
[wholeArc_intersects_escape_of_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma wholeArc_intersects_escape_of_far_eq
  {lo hi root far : Fin 2 -> Real}
  {crosscut : Path lo hi}
  {escape : Path root far}
-- given
  (hloRootX : lo 0 = root 0)
  (hhiRootX : hi 0 = root 0)
  (hloRootY : lo 1 < root 1)
  (hrootHiY : root 1 < hi 1)
  (hcrossLeft : ∀ t : unitInterval, lo 0 <= crosscut t 0)
  (hescapeLeft : ∀ t : unitInterval, root 0 <= escape t 0)
  (hfar : ∀ t : unitInterval, crosscut t 0 < far 0) :
-- imply
  ∃ t s : unitInterval, crosscut t = escape s := by
-- proof
  apply StatMech.ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape_of_far crosscut escape hloRootX hhiRootX hloRootY hrootHiY hcrossLeft hescapeLeft hfar

/--
[wholeArc_intersects_escape_of_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma wholeArc_intersects_escape_of_outside_eq
  {lo hi root far : Fin 2 -> Real}
  {crosscut : Path lo hi}
  {escape : Path root far}
-- given
  (hloRootX : lo 0 = root 0)
  (hhiRootX : hi 0 = root 0)
  (hloRootY : lo 1 < root 1)
  (hrootHiY : root 1 < hi 1)
  (hcrossLeft : ∀ t : unitInterval, lo 0 <= crosscut t 0)
  (hescapeLeft : ∀ t : unitInterval, root 0 <= escape t 0)
  (houtside : (∀ t : unitInterval, crosscut t 0 < far 0) ∨ (∀ t : unitInterval, crosscut t 1 < far 1) ∨ (∀ t : unitInterval, far 1 < crosscut t 1)) :
-- imply
  ∃ t s : unitInterval, crosscut t = escape s := by
-- proof
  apply StatMech.ContinuousHalfPlaneCrosscut.wholeArc_intersects_escape_of_outside crosscut escape hloRootX hhiRootX hloRootY hrootHiY hcrossLeft hescapeLeft houtside

/--
[exists_open_graphWalk_to_exposedRectExit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma exists_open_graphWalk_to_exposedRectExit_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {eta : ConfigSpace (Sym2 W)}
  {r right bottom top : Real}
  {x : W}
-- given
  (hxRect : x ∈ D.dualEmbedding.rectVertices r right bottom top)
  (hinfinite : (Pdual.clusterWithinSet eta (D.dualEmbedding.rightHalfPlaneVertices r) x).Infinite) :
-- imply
  ∃ z : W, ∃ q : Pdual.graph.Walk x z, ¬q.Nil ∧ (∀ v ∈ q.support, v ∈ D.dualEmbedding.rightHalfPlaneVertices r) ∧ (∀ {u v : W}, s(u, v) ∈ q.edges -> eta s(u, v) = true) ∧ (right < D.dualEmbedding.vertexCoord z 0 ∨ D.dualEmbedding.vertexCoord z 1 < bottom ∨ top < D.dualEmbedding.vertexCoord z 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_open_graphWalk_to_exposedRectExit D eta hxRect hinfinite

/--
[WholeArcBoundaryPlacement.toIncidence_of_exposedEndpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma toIncidence_of_exposedEndpoint_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {x y : V}
  {a b : W}
  {p : P.graph.Walk x y}
  {q : Pdual.graph.Walk a b}
  {right bottom top : Real}
-- given
  (hplace : WholeArcBoundaryPlacement D p q)
  (hcrossRight : ∀ t : unitInterval, D.primalEmbedding.coordinates (D.primalEmbedding.simpleWalkArc p t) 0 < right)
  (hcrossBottom : ∀ t : unitInterval, bottom < D.primalEmbedding.coordinates (D.primalEmbedding.simpleWalkArc p t) 1)
  (hcrossTop : ∀ t : unitInterval, D.primalEmbedding.coordinates (D.primalEmbedding.simpleWalkArc p t) 1 < top)
  (hexit : right < D.dualEmbedding.vertexCoord b 0 ∨ D.dualEmbedding.vertexCoord b 1 < bottom ∨ top < D.dualEmbedding.vertexCoord b 1) :
-- imply
  WholeArcBoundaryIncidence D p q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.WholeArcBoundaryPlacement.toIncidence_of_exposedEndpoint D hplace hcrossRight hcrossBottom hcrossTop hexit

/--
[no_open_primal_dual_of_wholeArcBoundaryIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma no_open_primal_dual_of_wholeArcBoundaryIncidence_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
  {a b : W}
  {p : P.graph.Walk x y}
  {q : Pdual.graph.Walk a b}
-- given
  (hp : ¬p.Nil)
  (hq : ¬q.Nil)
  (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges -> omega s(u, v) = true)
  (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges -> dualConfigEquiv D.edgeDual omega s(u, v) = true)
  (hinc : WholeArcBoundaryIncidence D p q) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_open_primal_dual_of_wholeArcBoundaryIncidence D omega p q hp hq hpopen hqopen hinc

/--
[no_open_primal_dual_of_wholeArcTraceIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean)
-/
@[path]
private lemma no_open_primal_dual_of_wholeArcTraceIncidence_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {omega : ConfigSpace (Sym2 V)}
  {x y : V}
  {a b : W}
  {p : P.graph.Walk x y}
  {q : Pdual.graph.Walk a b}
-- given
  (hp : ¬p.Nil)
  (hq : ¬q.Nil)
  (hpopen : ∀ {u v : V}, s(u, v) ∈ p.edges -> omega s(u, v) = true)
  (hqopen : ∀ {u v : W}, s(u, v) ∈ q.edges -> dualConfigEquiv D.edgeDual omega s(u, v) = true)
  (hinc : WholeArcTraceIncidence D p q) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.no_open_primal_dual_of_wholeArcTraceIncidence D omega p q hp hq hpopen hqopen hinc


-- created on 2026-10-23

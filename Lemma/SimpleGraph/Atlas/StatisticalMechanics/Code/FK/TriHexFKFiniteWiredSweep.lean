import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep.Part3
open Finset StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[triHexFK_finiteWiredBoundaryReachRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean)
-/
@[path]
private lemma triHexFK_finiteWiredBoundaryReachRatio_eq_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype V]
  [DecidableEq V]
  {q y0 y1 y2 y0Star y1Star y2Star : Real}
  {terminal : ι → Fin 3 → V}
  [DecidablePred boundary]
  {root : V}
-- given
  (hq : q ≠ 0)
  (hyprod : y0 * y1 * y2 ≠ 0)
  (h0 : y0 * y0Star = q)
  (h1 : y1 * y1Star = q)
  (h2 : y2 * y2Star = q)
  (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
  (boundary : V → Prop) :
-- imply
  starFKFiniteWiredBoundaryReachRatio q y0Star y1Star y2Star terminal boundary root = triangleFKFiniteWiredBoundaryReachRatio q y0 y1 y2 terminal boundary root := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_finiteWiredBoundaryReachRatio_eq hq hyprod h0 h1 h2 hsurface terminal boundary root

/--
[triHexFK_finiteWiredBoundaryReachRatio_eq_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean)
-/
@[path]
private lemma triHexFK_finiteWiredBoundaryReachRatio_eq_homogeneous_eq
  [Fintype ι]
  [DecidableEq ι]
  [Fintype V]
  [DecidableEq V]
  {q p : Real}
  {terminal : ι → Fin 3 → V}
  [DecidablePred boundary]
  {root : V}
-- given
  (hq : 0 < q)
  (hp : p ∈ Set.Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0)
  (boundary : V → Prop) :
-- imply
  starFKFiniteWiredBoundaryReachRatio q (FrontierA.fkEdgeOdds (BeffaraDC.dualParam p q)) (FrontierA.fkEdgeOdds (BeffaraDC.dualParam p q)) (FrontierA.fkEdgeOdds (BeffaraDC.dualParam p q)) terminal boundary root = triangleFKFiniteWiredBoundaryReachRatio q (FrontierA.fkEdgeOdds p) (FrontierA.fkEdgeOdds p) (FrontierA.fkEdgeOdds p) terminal boundary root := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_finiteWiredBoundaryReachRatio_eq_homogeneous hq hp hsurface terminal boundary root

/--
[TriHexFiniteWiredLevel.starBoundaryReachRatio_eq_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean)
-/
@[path]
private lemma starBoundaryReachRatio_eq_triangle_eq
  {D : TriHexFiniteWiredLevel}
  {q p : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Set.Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  D.starBoundaryReachRatio q p = D.triangleBoundaryReachRatio q p := by
-- proof
  apply StatMech.FK.PeriodicPlanar.TriHexFiniteWiredLevel.starBoundaryReachRatio_eq_triangle D hq hp hsurface

/--
[triHexFK_finiteWiredExhaustion_tendsto_iff_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean)
-/
@[path]
private lemma triHexFK_finiteWiredExhaustion_tendsto_iff_homogeneous_eq
  {D : Nat → TriHexFiniteWiredLevel}
  {q p theta : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Set.Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  Filter.Tendsto (fun n => (D n).starBoundaryReachRatio q p) Filter.atTop (nhds theta) ↔ Filter.Tendsto (fun n => (D n).triangleBoundaryReachRatio q p) Filter.atTop (nhds theta) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexFK_finiteWiredExhaustion_tendsto_iff_homogeneous D hq hp hsurface

/--
[hexagonalGraph_adj_triHexPlanarCellTerminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean)
-/
@[path]
private lemma hexagonalGraph_adj_triHexPlanarCellTerminal_eq
  {z : Site 2}
  {i : Fin 3} :
-- imply
  hexagonalGraph.Adj (z, false) (triHexPlanarCellTerminal z i, true) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.hexagonalGraph_adj_triHexPlanarCellTerminal z i

/--
[triangularGraph_adj_triHexPlanarCellTerminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean)
-/
@[path]
private lemma triangularGraph_adj_triHexPlanarCellTerminal_eq
  {z : Site 2}
  {i j : Fin 3}
-- given
  (hij : i ≠ j) :
-- imply
  triangularGraph.Adj (triHexPlanarCellTerminal z i) (triHexPlanarCellTerminal z j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triangularGraph_adj_triHexPlanarCellTerminal z i j hij

/--
[triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean)
-/
@[path]
private lemma triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous_eq
  {n : Nat}
  {q p : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Set.Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  (triHexPlanarFiniteWiredLevel n).starBoundaryReachRatio q p = (triHexPlanarFiniteWiredLevel n).triangleBoundaryReachRatio q p := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteWiredBoundaryReachRatio_eq_homogeneous n hq hp hsurface

/--
[triHexPlanarFiniteWiredBoundaryReach_tendsto_iff_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean)
-/
@[path]
private lemma triHexPlanarFiniteWiredBoundaryReach_tendsto_iff_homogeneous_eq
  {q p theta : Real}
-- given
  (hq : 0 < q)
  (hp : p ∈ Set.Ioo (0 : Real) 1)
  (hsurface : FrontierA.triangularFKCriticalPolynomial q (FrontierA.fkEdgeOdds p) = 0) :
-- imply
  Filter.Tendsto (fun n => (triHexPlanarFiniteWiredLevel n).starBoundaryReachRatio q p) Filter.atTop (nhds theta) ↔ Filter.Tendsto (fun n => (triHexPlanarFiniteWiredLevel n).triangleBoundaryReachRatio q p) Filter.atTop (nhds theta) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.triHexPlanarFiniteWiredBoundaryReach_tendsto_iff_homogeneous hq hp hsurface


-- created on 2026-10-23

import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredRootReduction.Part2
open Filter Set Topology StatMech StatMech.Universality


/--
[isingReflectedCenteredRadialGridCellPoint_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredRootReduction.lean)
-/
@[path]
private lemma isingReflectedCenteredRadialGridCellPoint_center_eq
  {n : Nat}
  {mesh : Real}
-- given
  (hn : 0 < n) :
-- imply
  isingReflectedCenteredRadialGridCellPoint mesh n (n - 1) (n - 1) (1 / 2) (1 / 2) = 0 := by
-- proof
  apply StatMech.Universality.isingReflectedCenteredRadialGridCellPoint_center n hn mesh

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_zero_eq_center_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredRootReduction.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_zero_eq_center_average_eq
  {k : Nat} :
-- imply
  fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k 0 = (fkIsingExpandingBoundarySquareCenteredRootNode k 0 0 + fkIsingExpandingBoundarySquareCenteredRootNode k 1 0 + fkIsingExpandingBoundarySquareCenteredRootNode k 0 1 + fkIsingExpandingBoundarySquareCenteredRootNode k 1 1) / 4 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_zero_eq_center_average k

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_center_nodes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredRootReduction.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_center_nodes_eq
-- given
  (target : Complex -> Complex)
  (hnode : forall a b : Fin 2, Tendsto (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k a b) atTop (nhds (target 0))) :
-- imply
  Tendsto (fun k => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_center_nodes target hnode

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_centeredNeighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredRootReduction.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_centeredNeighbor_eq
-- given
  (target : Complex -> Complex)
  (hneighbor : FKIsingExpandingCenteredNeighborTransport)
  (hbase : Tendsto (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds (target 0))) :
-- imply
  Tendsto (fun k => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_centeredNeighbor target hneighbor hbase

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_centeredStrictNeighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredRootReduction.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_centeredStrictNeighbor_eq
-- given
  (target : Complex -> Complex)
  (hneighbor : FKIsingExpandingCenteredStrictNeighborTransport)
  (hbase : Tendsto (fun k => fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds (target 0))) :
-- imply
  Tendsto (fun k => fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_of_centeredStrictNeighbor target hneighbor hbase


-- created on 2026-10-23

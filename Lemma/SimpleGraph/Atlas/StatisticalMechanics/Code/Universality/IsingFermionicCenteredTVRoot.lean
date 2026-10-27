import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTVRoot
open Filter Set Topology StatMech StatMech.Universality


/--
[fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRoot.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV_eq
  {k : Nat}
-- given
  (hk : 2 ≤ k) :
-- imply
  ‖fkIsingExpandingBoundarySquareCenteredRootNode k 1 0 - fkIsingExpandingBoundarySquareCenteredRootNode k 1 1‖ ≤ fkIsingExpandingSquareScale k * 2432 ∧ ‖fkIsingExpandingBoundarySquareCenteredRootNode k 1 1 - fkIsingExpandingBoundarySquareCenteredRootNode k 0 1‖ ≤ fkIsingExpandingSquareScale k * 2432 ∧ ‖fkIsingExpandingBoundarySquareCenteredRootNode k 0 1 - fkIsingExpandingBoundarySquareCenteredRootNode k 0 0‖ ≤ fkIsingExpandingSquareScale k * 2432 ∧ ‖fkIsingExpandingBoundarySquareCenteredRootNode k 0 0 - fkIsingExpandingBoundarySquareCenteredRootNode k 1 0‖ ≤ fkIsingExpandingSquareScale k * 2432 := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredRootNode_edges_le_fullCarrierTV k hk

/--
[fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_fullCarrierTV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRoot.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_fullCarrierTV_eq
  {target : Complex → Complex}
-- given
  (hbase : Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds (target 0))) :
-- imply
  Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredReflectedInterpolant_root_tendsto_fullCarrierTV target hbase

/--
[fkIsingExpandingBoundarySquareCenteredRootNode_sub_base_tendsto_fullCarrierTV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRoot.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredRootNode_sub_base_tendsto_fullCarrierTV_eq
  {a b : Fin 2} :
-- imply
  Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k a b - fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredRootNode_sub_base_tendsto_fullCarrierTV a b

/--
[fkIsingExpandingBoundarySquareCenteredRootNode_tendsto_iff_root_tendsto_fullCarrierTV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTVRoot.lean)
-/
@[path]
private lemma fkIsingExpandingBoundarySquareCenteredRootNode_tendsto_iff_root_tendsto_fullCarrierTV_eq
  {target : Complex → Complex} :
-- imply
  Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCenteredRootNode k 0 0) atTop (nhds (target 0)) ↔ Tendsto (fun k ↦ fkIsingExpandingBoundarySquareCenteredReflectedInterpolant k fkIsingExpandingBoundarySquareCaratheodoryApproximation.root) atTop (nhds (target fkIsingExpandingBoundarySquareCaratheodoryApproximation.root)) := by
-- proof
  apply StatMech.Universality.fkIsingExpandingBoundarySquareCenteredRootNode_tendsto_iff_root_tendsto_fullCarrierTV target


-- created on 2026-10-23

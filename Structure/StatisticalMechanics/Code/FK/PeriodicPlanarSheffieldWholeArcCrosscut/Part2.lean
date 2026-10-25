/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldWholeArcCrosscut.Part2
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

structure WholeArcTraceIncidence
    (D : PeriodicPlanarDualPair P Pdual)
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b) where
  lo : Fin 2 -> Real
  hi : Fin 2 -> Real
  root : Fin 2 -> Real
  far : Fin 2 -> Real
  primalTrace : Path lo hi
  dualTrace : Path root far
  primal_range : Set.range primalTrace ⊆ Set.range
    ((D.primalEmbedding.simpleWalkArc p).map
      D.primalEmbedding.coordinates.continuous)
  dual_range : Set.range dualTrace ⊆ Set.range
    ((D.dualEmbedding.simpleWalkArc q).map
      D.dualEmbedding.coordinates.continuous)
  lower_boundary : lo 0 = root 0
  upper_boundary : hi 0 = root 0
  root_above_lower : lo 1 < root 1
  root_below_upper : root 1 < hi 1
  primal_in_halfPlane : ∀ t : unitInterval,
    lo 0 <= primalTrace t 0
  dual_in_halfPlane : ∀ t : unitInterval,
    root 0 <= dualTrace t 0
  dual_endpoint_outside :
    (∀ t : unitInterval, primalTrace t 0 < far 0) ∨
    (∀ t : unitInterval, primalTrace t 1 < far 1) ∨
    (∀ t : unitInterval, far 1 < primalTrace t 1)


end PeriodicPlanarDualPair
end FK.PeriodicPlanar
end StatMech

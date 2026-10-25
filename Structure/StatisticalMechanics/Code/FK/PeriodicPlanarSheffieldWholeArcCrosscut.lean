/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldWholeArcCrosscut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldWholeArcCrosscut
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace FK.PeriodicPlanar

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

structure WholeArcBoundaryPlacement
    (D : PeriodicPlanarDualPair P Pdual)
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b) : Prop where
  lower_boundary : D.primalEmbedding.vertexCoord x 0 =
    D.dualEmbedding.vertexCoord a 0
  upper_boundary : D.primalEmbedding.vertexCoord y 0 =
    D.dualEmbedding.vertexCoord a 0
  root_above_lower : D.primalEmbedding.vertexCoord x 1 <
    D.dualEmbedding.vertexCoord a 1
  root_below_upper : D.dualEmbedding.vertexCoord a 1 <
    D.primalEmbedding.vertexCoord y 1
  primal_in_halfPlane : ∀ t : unitInterval,
    D.primalEmbedding.vertexCoord x 0 <=
      D.primalEmbedding.coordinates
        (D.primalEmbedding.simpleWalkArc p t) 0
  dual_in_halfPlane : ∀ t : unitInterval,
    D.dualEmbedding.vertexCoord a 0 <=
      D.dualEmbedding.coordinates
        (D.dualEmbedding.simpleWalkArc q t) 0


structure WholeArcBoundaryIncidence
    (D : PeriodicPlanarDualPair P Pdual)
    {x y : V} {a b : W}
    (p : P.graph.Walk x y) (q : Pdual.graph.Walk a b) : Prop
    extends WholeArcBoundaryPlacement D p q where
  dual_endpoint_outside :
    (∀ t : unitInterval,
      D.primalEmbedding.coordinates
          (D.primalEmbedding.simpleWalkArc p t) 0 <
        D.dualEmbedding.vertexCoord b 0) ∨
    (∀ t : unitInterval,
      D.primalEmbedding.coordinates
          (D.primalEmbedding.simpleWalkArc p t) 1 <
        D.dualEmbedding.vertexCoord b 1) ∨
    (∀ t : unitInterval,
      D.dualEmbedding.vertexCoord b 1 <
        D.primalEmbedding.coordinates
          (D.primalEmbedding.simpleWalkArc p t) 1)


end PeriodicPlanarDualPair
end FK.PeriodicPlanar
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part7
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t -
        D.primalEmbedding.vertex x) i| <= B
  dualArcBound : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t -
        D.dualEmbedding.vertex x) i| <= B
  padding : Nat
  padding_ge : 4 * B <= (padding : Real)
  scheduleData : PairedAdjacentBoundaryBandScheduleData
    D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) (fun _ => 0)
  array : PairedAdjacentCrossNestedOutwardArrayData
    D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu)
      scheduleData padding (fun n => n)
  extentX_large : forall n j, 10 * B < (array.chain n).extentX j
  extentY_large : forall n j, 10 * B < (array.chain n).extentY j


end StatMech.FK.PeriodicPlanar

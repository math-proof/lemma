/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldEndpointClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceClosure.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part8
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.ExpandedEndpointSheffieldCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  B : Real
  Bpos : 0 < B
  primalArcBound : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
    |D.primalEmbedding.coordinates
      (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B
  dualArcBound : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2),
    |D.dualEmbedding.coordinates
      (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B
  template : Nat -> Finset V
  radius : Nat -> Nat
  step : Nat -> Int
  vLeft : Nat -> Real
  vRight : Nat -> Real
  vBottom : Nat -> Real
  vTop : Nat -> Real
  hLeft : Nat -> Real
  hRight : Nat -> Real
  hBottom : Nat -> Real
  hTop : Nat -> Real
  pad : Nat -> Real
  level : ExpandedEndpointPrimalBoundaryBandLevel D.primalEmbedding mu
    template radius vLeft vRight vBottom vTop pad
  continuation :
    D.primalEmbedding.UniformTemplateAdjacentBoundaryBandCrossingRadius
      mu template step radius
  alignLeft : forall n, hLeft n + pad n = vLeft n - pad n
  alignRight : forall n, hRight n - pad n = vRight n + pad n
  alignBottom : forall n, hBottom n - pad n = vBottom n + pad n
  alignTop : forall n, hTop n + pad n = vTop n - pad n + step n
  pad_ge : forall n, 4 * B <= pad n
  verticalWidth : forall n, 10 * B < vRight n - vLeft n
  verticalHeight : forall n, 10 * B < vTop n - vBottom n
  horizontalWidth : forall n, 10 * B < hRight n - hLeft n
  horizontalHeight : forall n, 10 * B < hTop n - hBottom n
  dualVertical : Tendsto (fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1)
  dualHorizontal : Tendsto (fun n => mu.real
    ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1)


end StatMech.FK.PeriodicPlanar

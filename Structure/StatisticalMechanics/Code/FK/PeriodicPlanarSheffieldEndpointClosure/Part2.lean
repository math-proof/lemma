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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldEndpointClosure
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice BeffaraDC

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PeriodicPlanarDualPair.BranchAlignedOutwardEndpointCertificate
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
  branch : Nat -> Bool
  a : Nat -> Real
  b : Nat -> Real
  c : Nat -> Real
  d : Nat -> Real
  xPad : Nat -> Real
  yPad : Nat -> Real
  vLeft : Nat -> Real
  vRight : Nat -> Real
  vBottom : Nat -> Real
  vTop : Nat -> Real
  hLeft : Nat -> Real
  hRight : Nat -> Real
  hBottom : Nat -> Real
  hTop : Nat -> Real
  vLeft_eq : forall n, vLeft n = a n + xPad n
  vRight_eq : forall n, vRight n = b n - xPad n
  vBottom_eq : forall n, vBottom n = c n
  vTop_eq : forall n, vTop n = d n
  hLeft_eq : forall n, hLeft n = a n
  hRight_eq : forall n, hRight n = b n
  hBottom_eq : forall n, hBottom n = c n + yPad n
  hTop_eq : forall n, hTop n = d n - yPad n
  xPad_ge : forall n, 4 * B <= xPad n
  yPad_ge : forall n, 4 * B <= yPad n
  outerWidth : forall n, a n + 5 * B < b n - 5 * B
  outerHeight : forall n, c n + 5 * B < d n - 5 * B
  primalSelected : Tendsto (fun n => if branch n then
    mu.real (D.primalEmbedding.verticalCrossingEvent
      (vLeft n) (vRight n) (vBottom n) (vTop n))
  else
    mu.real (D.primalEmbedding.horizontalCrossingEvent
      (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1)
  dualSelected : Tendsto (fun n => if branch n then
    mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.horizontalCrossingEvent
        (hLeft n) (hRight n) (hBottom n) (hTop n))
  else
    mu.real ((dualConfigEquiv D.edgeDual) ⁻¹'
      D.dualEmbedding.verticalCrossingEvent
        (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1)


end StatMech.FK.PeriodicPlanar

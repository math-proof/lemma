/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldNearBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneInfiniteArm
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldApproximatePreference.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.leftBoundaryExhaustionVertices
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat) : Set V :=
  E.rectVertices r (r + n) (-(n : Real)) n


def PeriodicPlaneEmbedding.leftBoundaryExhaustionEvent
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) (n : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  E.rectSideConnectionEvent r (r + n) (-(n : Real)) n S
    (E.rectLeftBoundaryVertices r (r + n) (-(n : Real)) n)

end StatMech.FK.PeriodicPlanar

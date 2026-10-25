/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualTransverse
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicGraph.finiteSetHitsInfinite
    (P : PeriodicGraph V) (L : Finset V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ L, (P.cluster omega x).Infinite}

end StatMech.FK.PeriodicPlanar

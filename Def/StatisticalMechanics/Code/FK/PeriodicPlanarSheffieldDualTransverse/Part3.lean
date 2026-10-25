/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualTransverse.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualTransverse.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicGraph.finiteInfinitePairConnectionEvent
    (P : PeriodicGraph V) (L R : Finset V) (N : Nat) :
    Set (ConfigSpace (Sym2 V)) :=
  (P.finiteSetHitsInfinite L ∩ P.finiteSetHitsInfinite R) \
    P.pairMergeErrorUnion L R N

end StatMech.FK.PeriodicPlanar

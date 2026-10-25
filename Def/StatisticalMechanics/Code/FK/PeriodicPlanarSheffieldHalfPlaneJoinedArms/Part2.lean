/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneJoinedArms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneInfiniteArm
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneStripUnion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArms
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.finiteJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (L : Set V)
      (E.lowerBoundaryRayVertices r c) ∩
    P.infiniteSetConnectionWithin (E.rightHalfPlaneVertices r) (R : Set V)
      (E.upperBoundaryRayVertices r d)) \
    E.halfPlaneStripPairMergeErrorUnion r n L R

end StatMech.FK.PeriodicPlanar

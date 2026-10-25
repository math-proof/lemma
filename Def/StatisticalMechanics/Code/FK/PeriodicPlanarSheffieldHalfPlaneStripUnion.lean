/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneStripUnion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneMerge
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneStrip.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.halfPlaneStripPairMergeErrorUnion
    (E : PeriodicPlaneEmbedding P) (r : Real) (n : Nat)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  ⋃ p : ↥(L.product R),
    E.halfPlaneStripPairMergeError r n p.1.1 p.1.2

end StatMech.FK.PeriodicPlanar

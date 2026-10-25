/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicGraph.clusterWithinSet
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V))
    (A : Set V) (x : V) : Set V :=
  {y | omega ∈ P.connectedWithinSet A x y}

end StatMech.FK.PeriodicPlanar

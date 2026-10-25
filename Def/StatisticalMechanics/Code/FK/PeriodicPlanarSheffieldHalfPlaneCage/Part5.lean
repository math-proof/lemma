/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrosscut
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part8
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotated
import Mathlib.Topology.Subpath
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part5
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.finiteJoinedBoundaryArmAt
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) (b u : V) : Set (ConfigSpace (Sym2 V)) :=
  {omega |
    b ∈ E.lowerBoundaryRayVertices r c ∧
    u ∈ E.upperBoundaryRayVertices r d ∧
    ∃ x ∈ L, (P.cluster omega x).Infinite ∧
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧
    ∃ y ∈ R, (P.cluster omega y).Infinite ∧
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧
      omega ∈ P.connectedWithinSet
        (E.rightHalfPlaneStripVertices r n) x y}

end StatMech.FK.PeriodicPlanar

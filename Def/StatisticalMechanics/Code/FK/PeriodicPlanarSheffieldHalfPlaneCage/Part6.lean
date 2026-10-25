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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part6
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.finiteOpenExitedJoinedBoundaryArmEvent
    (E : PeriodicPlaneEmbedding P) (r c d : Real) (n : Nat)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  {omega |
    ∃ b ∈ E.lowerBoundaryRayVertices r c, ∃ z : V,
      P.graph.Adj b z ∧ z ∉ E.rightHalfPlaneVertices r ∧
      omega s(b, z) = true ∧
    ∃ x ∈ L, (P.cluster omega x).Infinite ∧
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b ∧
    ∃ u ∈ E.upperBoundaryRayVertices r d, ∃ w : V,
      P.graph.Adj u w ∧ w ∉ E.rightHalfPlaneVertices r ∧
      omega s(u, w) = true ∧
    ∃ y ∈ R, (P.cluster omega y).Infinite ∧
      omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) y u ∧
      omega ∈ P.connectedWithinSet
        (E.rightHalfPlaneStripVertices r n) x y}

end StatMech.FK.PeriodicPlanar

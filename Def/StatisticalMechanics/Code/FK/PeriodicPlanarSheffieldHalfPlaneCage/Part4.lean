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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part4
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.infiniteOpenBoundaryConnection
    (E : PeriodicPlaneEmbedding P) (r : Real) (S : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, (P.cluster omega x).Infinite ∧
    ∃ b ∈ E.rightHalfPlaneBoundaryVertices r,
      ∃ z : V, P.graph.Adj b z ∧ z ∉ E.rightHalfPlaneVertices r ∧
        omega s(b, z) = true ∧
        omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b}


def PeriodicPlaneEmbedding.infiniteOpenBoundaryConnectionTo
    (E : PeriodicPlaneEmbedding P) (r : Real) (S T : Set V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ x ∈ S, (P.cluster omega x).Infinite ∧
    ∃ b ∈ T, b ∈ E.rightHalfPlaneBoundaryVertices r ∧
      ∃ z : V, P.graph.Adj b z ∧ z ∉ E.rightHalfPlaneVertices r ∧
        omega s(b, z) = true ∧
        omega ∈ P.connectedWithinSet (E.rightHalfPlaneVertices r) x b}

end StatMech.FK.PeriodicPlanar

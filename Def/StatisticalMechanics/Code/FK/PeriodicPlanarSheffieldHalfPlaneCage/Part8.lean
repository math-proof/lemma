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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage.Part8
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def PeriodicPlaneEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
    (E : PeriodicPlaneEmbedding P) (r c d : Real) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | ∃ b ∈ E.rightHalfPlaneBoundaryVertices r,
    c ≤ E.vertexCoord b 1 ∧ E.vertexCoord b 1 ≤ d ∧
    (P.clusterWithinSet omega (E.rightHalfPlaneVertices r) b).Infinite}

end StatMech.FK.PeriodicPlanar

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


theorem PeriodicGraph.degree_shift (P : PeriodicGraph V) (z : Lattice.Site 2) (v : V) :
    P.vertexDegree (P.shift z v) = P.vertexDegree v := by
  unfold PeriodicGraph.vertexDegree
  rw [← @SimpleGraph.card_neighborSet_eq_degree V P.graph (P.shift z v)
      (P.locallyFinite _),
    ← @SimpleGraph.card_neighborSet_eq_degree V P.graph v (P.locallyFinite _)]
  exact (@Fintype.card_congr _ _ (P.locallyFinite _) (P.locallyFinite _)
    ((P.shiftIso z).mapNeighborSet v)).symm


end StatMech.FK.PeriodicPlanar

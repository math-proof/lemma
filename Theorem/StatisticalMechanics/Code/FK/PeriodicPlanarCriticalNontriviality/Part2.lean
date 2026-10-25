/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalNontriviality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarPercolationApproximation.Part3
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalNontriviality.Part2
open MeasureTheory Set SimpleGraph Filter Topology
open scoped Classical BigOperators


namespace StatMech.FK.PeriodicPlanar

universe u

variable {V : Type u} [DecidableEq V]


theorem PeriodicGraph.degree_le_degreeBound (P : PeriodicGraph V) (v : V) :
    P.vertexDegree v ≤ P.degreeBound := by
  obtain ⟨z, u, hu, rfl⟩ := P.covers v
  rw [P.degree_shift]
  exact Finset.le_sup hu


end StatMech.FK.PeriodicPlanar

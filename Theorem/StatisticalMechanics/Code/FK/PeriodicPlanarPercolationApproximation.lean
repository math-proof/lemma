/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarPercolationApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarParameterMonotonicity.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in


theorem reachable_induce_innerBoundary
    (G : SimpleGraph V) (S : Set V) {x z : V}
    (hx : x ∈ S) (hz : z ∉ S) (hreach : G.Reachable x z) :
    ∃ y : S, (G.induce S).Reachable ⟨x, hx⟩ y ∧
      ∃ w : V, G.Adj y.1 w ∧ w ∉ S := by
  obtain ⟨p⟩ := hreach
  induction p with
  | nil => exact (hz hx).elim
  | @cons x y z hxy p ih =>
      by_cases hy : y ∈ S
      · obtain ⟨v, hv, w, hvw, hw⟩ := ih hy hz
        refine ⟨v, ?_, w, hvw, hw⟩
        exact ((show (G.induce S).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy).reachable).trans hv
      · exact ⟨⟨x, hx⟩, .refl _, y, hxy, hy⟩

theorem PeriodicGraph.root_mem_orbitBox_zero (P : PeriodicGraph V) :
    P.root ∈ P.orbitBox 0 := by
  rw [P.mem_orbitBox_iff]
  refine ⟨0, by simp, P.root, P.root_mem_fundamentalDomain, ?_⟩
  rw [P.shift_zero]
  rfl


end StatMech.FK.PeriodicPlanar

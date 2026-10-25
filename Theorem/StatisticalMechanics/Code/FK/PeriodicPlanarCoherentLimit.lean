/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCoherentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.FK.BulkDeviationProof.Part2
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
open Finset Set SimpleGraph MeasureTheory Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

variable {V : Type*} [DecidableEq V]

theorem PeriodicGraph.finite_subset_orbitBox (P : PeriodicGraph V)
    (S : Finset V) :
    ∃ n, ∀ v ∈ S, v ∈ P.orbitBox n := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a S ha ih =>
      obtain ⟨na, haBox⟩ := P.mem_orbitBox_of_eventually a
      obtain ⟨nS, hSBox⟩ := ih
      refine ⟨max na nS, ?_⟩
      intro v hv
      rw [Finset.mem_insert] at hv
      rcases hv with rfl | hv
      · exact P.orbitBox_mono (Nat.le_max_left _ _) haBox
      · exact P.orbitBox_mono (Nat.le_max_right _ _) (hSBox v hv)


theorem PeriodicGraph.exists_buffer_radius (P : PeriodicGraph V) (n : ℕ) :
    ∃ m, n < m ∧
      ∀ v ∈ P.orbitBox n, ∀ w, P.graph.Adj v w → w ∈ P.orbitBox m := by
  classical
  letI : SimpleGraph.LocallyFinite P.graph := P.locallyFinite
  let neighborUnion := (P.orbitBox n).biUnion
    (fun v => P.graph.neighborFinset v)
  obtain ⟨k, hk⟩ := P.finite_subset_orbitBox neighborUnion
  refine ⟨max (n + 1) k, Nat.lt_of_lt_of_le (Nat.lt_succ_self n)
    (Nat.le_max_left _ _), ?_⟩
  intro v hv w hvw
  have hw : w ∈ neighborUnion := by
    rw [Finset.mem_biUnion]
    exact ⟨v, hv, by simpa only [SimpleGraph.mem_neighborFinset] using hvw⟩
  exact P.orbitBox_mono (Nat.le_max_right _ _) (hk w hw)


end PeriodicPlanar
end FK
end StatMech

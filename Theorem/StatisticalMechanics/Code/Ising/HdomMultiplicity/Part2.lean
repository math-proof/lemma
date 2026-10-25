/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Def.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem hmu_tri_conn (a b : Fin 3) (hab : a ≠ b) :
    connP (oddEdges (hmu_TriG.edgeFinset) hmu_triM) a b := by
  apply Relation.ReflTransGen.single
  refine ⟨s(a, b), ?_, Sym2.mem_mk_left a b, Sym2.mem_mk_right a b, hab⟩
  rw [oddEdges, Finset.mem_filter]
  exact ⟨by rw [SimpleGraph.mem_edgeFinset]; exact hab, ⟨0, rfl⟩⟩


theorem hmu_tri_allConn : hnw_allConn hmu_TriG hmu_triM 0 1 2 :=
  ⟨hmu_tri_conn 1 2 (by decide), hmu_tri_conn 0 2 (by decide), hmu_tri_conn 0 1 (by decide)⟩


theorem hmu_tri_src : Sharpness.sources hmu_TriG hmu_triM = (∅ : Finset (Fin 3)) := by
  ext z
  simp only [Sharpness.mem_sources]
  constructor
  · intro h
    exfalso
    have hflux : Sharpness.incidentFlux hmu_TriG hmu_triM z = 2 := by
      unfold Sharpness.incidentFlux hmu_triM
      rw [Finset.sum_const, smul_eq_mul, mul_one]
      fin_cases z <;> decide
    rw [hflux] at h
    exact (Nat.not_odd_iff_even.mpr ⟨1, rfl⟩) h
  · intro h; exact absurd h (Finset.notMem_empty z)


theorem hmu_hdom_refutable :
    ¬ (2 * (∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter
            (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅)
        ≤ ∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter
            (fun m => hnw_noneConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) := by
  have hall : ({hmu_triM} : Finset (Current (Fin 3))).filter
      (fun m => hnw_allConn hmu_TriG m 0 1 2) = {hmu_triM} := by
    rw [Finset.filter_eq_self]
    intro m hm; rw [Finset.mem_singleton] at hm; subst hm; exact hmu_tri_allConn
  have hnone : ({hmu_triM} : Finset (Current (Fin 3))).filter
      (fun m => hnw_noneConn hmu_TriG m 0 1 2) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro m hm; rw [Finset.mem_singleton] at hm; subst hm
    intro hcon; exact hnw_noneConn_not_allConn hmu_TriG hmu_triM hcon hmu_tri_allConn
  rw [hall, hnone, Finset.sum_singleton, Finset.sum_empty, not_le]
  have hmass_pos : 0 < hnw_mass hmu_TriG 1 (fun _ => 1) hmu_triM ∅ := by
    have := hmu_mass_pos hmu_TriG 1 (fun _ => 1) (by norm_num) (by intro e; norm_num) hmu_triM
    rwa [hmu_tri_src] at this
  linarith

end Ising
end StatMech

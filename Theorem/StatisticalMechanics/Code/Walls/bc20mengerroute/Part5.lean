/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc20mengerroute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.bc19menger.Part5
import Theorem.StatisticalMechanics.Code.Percolation.MengerRouting.Part3
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Def.StatisticalMechanics.Code.Walls.bc20mengerroute.Part5
open StatMech.Lattice StatMech.ConfigSpace SimpleGraph
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech.Walls

variable {d : ℕ}


universe u

variable {V : Type u} [DecidableEq V] {GG : SimpleGraph V}

theorem bc20_mengerCore_of_originBranchSurvival (d : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (h : bc20_OriginBranchSurvival d ω) : MengerCore ω := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, ⟨hd12, hd13, hd23⟩, hinf⟩ := h
  exact mng_mengerCore_of_neighborClusters ω a₁ a₂ a₃ hne hadj hinf
    ⟨bc20_removeSite_cluster_ne ω a₁ a₂ hd12,
      bc20_removeSite_cluster_ne ω a₁ a₃ hd13,
      bc20_removeSite_cluster_ne ω a₂ a₃ hd23⟩


theorem bc20_mengerRoutingCover_of_originBranchSurvival (d n : ℕ)
    (h : ∀ ω ∈ threeMeetBox d n, bc20_OriginBranchSurvival d ω) :
    MengerRoutingCover d n :=
  fun ω hω => bc20_mengerCore_of_originBranchSurvival d ω (h ω hω)


theorem bc20_removeSite_infinite_of_originFree (ω : ConfigSpace (Sym2 (Site d))) (a : Site d)
    (h0 : (0 : Site d) ∉ cluster d ω a) (hinf : (cluster d ω a).Infinite) :
    (cluster d (removeSite 0 ω) a).Infinite := by
  rw [cluster_infinite_iff]
  intro m
  obtain ⟨z, hzb, hconn⟩ := (cluster_infinite_iff ω a).mp hinf m
  obtain ⟨w⟩ := hconn
  refine ⟨z, hzb, bc20_connected_removeSite_of_avoiding ω w (fun hmem => h0 ?_)⟩
  rw [cluster_eq_of_connected w.reachable]
  exact ava_support_mem_cluster ω w hmem


theorem bc20_originBranchSurvival_of_originFree (d : ℕ) (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hdist : cluster d ω a₁ ≠ cluster d ω a₂ ∧ cluster d ω a₁ ≠ cluster d ω a₃ ∧
      cluster d ω a₂ ≠ cluster d ω a₃)
    (h0 : (0 : Site d) ∉ cluster d ω a₁ ∧ (0 : Site d) ∉ cluster d ω a₂ ∧
      (0 : Site d) ∉ cluster d ω a₃)
    (hinf : (cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧
      (cluster d ω a₃).Infinite) :
    bc20_OriginBranchSurvival d ω :=
  ⟨a₁, a₂, a₃, hne, hadj, hdist,
    bc20_removeSite_infinite_of_originFree ω a₁ h0.1 hinf.1,
    bc20_removeSite_infinite_of_originFree ω a₂ h0.2.1 hinf.2.1,
    bc20_removeSite_infinite_of_originFree ω a₃ h0.2.2 hinf.2.2⟩


end StatMech.Walls

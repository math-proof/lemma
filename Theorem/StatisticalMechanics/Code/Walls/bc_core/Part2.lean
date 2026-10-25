/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc_cutmeetsaxis
import Theorem.StatisticalMechanics.Code.Walls.bc_mouthcorridor
import Theorem.StatisticalMechanics.Code.Walls.bc_raydisjoint
import Theorem.StatisticalMechanics.Code.Walls.bc_forcemono
import Def.StatisticalMechanics.Code.Walls.bc_core.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc_boxReachesRay_of_boxNearAxis {n : ℕ} (h : bc_BoxNearAxis d n) :
    lma_BoxClusterReachesRay d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨j₁, j₂, j₃, h1, h2, h3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨j₁, j₂, j₃, bc_clusterReachesRay_of_nearAxis ω x₁ j₁ h1,
    bc_clusterReachesRay_of_nearAxis ω x₂ j₂ h2, bc_clusterReachesRay_of_nearAxis ω x₃ j₃ h3⟩


theorem bc_boxAttachData_of_boxNearAxis {n : ℕ} (h : bc_BoxNearAxis d n) :
    tex_BoxAttachData d n :=
  lma_boxAttachData_of_reachesRay (bc_boxReachesRay_of_boxNearAxis h)


theorem bc_disjointRouting_of_boxNearAxis {n : ℕ} (h : bc_BoxNearAxis d n) :
    hrHD_DisjointRouting d n :=
  lma_disjointRouting_of_reachesRay (bc_boxReachesRay_of_boxNearAxis h)


theorem bc_boxNearAxis_of_boxAxisAssignment {n : ℕ} (h : lmg_BoxAxisAssignment d n) :
    bc_BoxNearAxis d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨j₁, j₂, j₃, _, ha1, ha2, ha3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact ⟨j₁, j₂, j₃, bc_nearAxis_of_axisAssignment ω x₁ j₁ ha1,
    bc_nearAxis_of_axisAssignment ω x₂ j₂ ha2, bc_nearAxis_of_axisAssignment ω x₃ j₃ ha3⟩


theorem bc_disjointRouting_of_boxAxisAssignment {n : ℕ} (h : lmg_BoxAxisAssignment d n) :
    hrHD_DisjointRouting d n :=
  bc_disjointRouting_of_boxNearAxis (bc_boxNearAxis_of_boxAxisAssignment h)


theorem bc_nearAxis_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    bc_NearAxis ω (hrHD_rayPt j 1) j :=
  ⟨self_mem_cluster ω (hrHD_rayPt j 1), connected_rfl, hinf⟩


theorem bc_clusterReachesRay_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    lma_ClusterReachesRay ω (hrHD_rayPt j 1) j :=
  bc_clusterReachesRay_of_nearAxis ω (hrHD_rayPt j 1) j (bc_nearAxis_neighbour ω j hinf)


theorem bc_attachData_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d}
    (hcd12 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1))
    (hcd13 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hcd23 : cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
    tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) :=
  lma_attachData_of_three_reachesRay ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)
    j₁ j₂ j₃ hcd12 hcd13 hcd23
    (bc_clusterReachesRay_neighbour ω j₁ hi1) (bc_clusterReachesRay_neighbour ω j₂ hi2)
    (bc_clusterReachesRay_neighbour ω j₃ hi3)


theorem bc_core (n : ℕ) :
    (bc_BoxNearAxis d n →
        tex_BoxAttachData d n ∧ hrHD_DisjointRouting d n) ∧
      (∀ {j₁ j₂ j₃ : Fin d} (ω : ConfigSpace (Sym2 (Site d))),
        cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1) →
        cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1) →
        cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1) →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite →
        (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite →
        tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) :=
  ⟨fun h => ⟨bc_boxAttachData_of_boxNearAxis h, bc_disjointRouting_of_boxNearAxis h⟩,
    fun ω hcd12 hcd13 hcd23 hi1 hi2 hi3 =>
      bc_attachData_of_neighbour_witnesses ω hcd12 hcd13 hcd23 hi1 hi2 hi3⟩

end Walls
end StatMech

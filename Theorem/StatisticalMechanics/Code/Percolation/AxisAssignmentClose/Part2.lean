/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/AxisAssignmentClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
import Def.StatisticalMechanics.Code.Percolation.AxisAssignmentClose.Part2
open MeasureTheory Set Finset
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem caa_boxClusterReachesRay {n : ℕ} (h : caa_BoxRunsAlongCandidates d n) :
    lma_BoxClusterReachesRay d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨S, hcand⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨j, _, hreach⟩ := caa_three_reachesRay ω ![x₁, x₂, x₃] S hcand
  exact ⟨j 0, j 1, j 2, hreach 0, hreach 1, hreach 2⟩


theorem caa_disjointRouting {n : ℕ} (h : caa_BoxRunsAlongCandidates d n) :
    hrHD_DisjointRouting d n :=
  lma_disjointRouting_of_reachesRay (caa_boxClusterReachesRay h)


theorem caa_candidates_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (a : Fin 3 → Fin d) (ha : Function.Injective a)
    (hinf : ∀ i : Fin 3, (cluster d (removeSite 0 ω) (hrHD_rayPt (a i) 1)).Infinite) :
    caa_RunsAlongCandidates ω (fun i => hrHD_rayPt (a i) 1)
      (fun i => ({a i} : Finset (Fin d))) := by
  refine ⟨?_, caa_hall_of_injective_singletons a ha⟩
  intro i j hj
  rw [Finset.mem_singleton] at hj
  subst hj
  exact crr_runsAlongAxis_of_neighbour ω (a i) (hinf i)


theorem caa_nonvacuous_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    (a : Fin 3 → Fin d) (ha : Function.Injective a)
    (hinf : ∀ i : Fin 3, (cluster d (removeSite 0 ω) (hrHD_rayPt (a i) 1)).Infinite) :
    (∃ j : Fin 3 → Fin d, (j 0 ≠ j 1 ∧ j 0 ≠ j 2 ∧ j 1 ≠ j 2) ∧
        (∀ i : Fin 3, lma_ClusterReachesRay ω (hrHD_rayPt (a i) 1) (j i))) ∧
      (hrHD_rayPt (a 0) 1 ≠ hrHD_rayPt (a 1) 1 ∧
        hrHD_rayPt (a 0) 1 ≠ hrHD_rayPt (a 2) 1 ∧
        hrHD_rayPt (a 1) 1 ≠ hrHD_rayPt (a 2) 1) := by
  have hcand := caa_candidates_neighbour_witnesses ω a ha hinf
  refine ⟨caa_three_reachesRay ω (fun i => hrHD_rayPt (a i) 1) _ hcand, ?_, ?_, ?_⟩
  · exact hrHD_rayPt_one_ne_of_ne (fun he => absurd (ha he) (by decide))
  · exact hrHD_rayPt_one_ne_of_ne (fun he => absurd (ha he) (by decide))
  · exact hrHD_rayPt_one_ne_of_ne (fun he => absurd (ha he) (by decide))

end Percolation
end StatMech

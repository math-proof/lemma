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
import Def.StatisticalMechanics.Code.Percolation.AxisAssignmentClose
open MeasureTheory Set Finset
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem caa_axisAssignment (ω : ConfigSpace (Sym2 (Site d))) (x : Fin 3 → Site d)
    (S : Fin 3 → Finset (Fin d)) (h : caa_RunsAlongCandidates ω x S) :
    ∃ f : Fin 3 → Fin d, Function.Injective f ∧
      ∀ i : Fin 3, crr_ClusterRunsAlongAxis ω (x i) (f i) := by
  obtain ⟨hruns, hHall⟩ := h
  obtain ⟨f, hinj, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective S).mp hHall
  exact ⟨f, hinj, fun i => hruns i (f i) (hmem i)⟩


theorem caa_three_reachesRay (ω : ConfigSpace (Sym2 (Site d))) (x : Fin 3 → Site d)
    (S : Fin 3 → Finset (Fin d)) (h : caa_RunsAlongCandidates ω x S) :
    ∃ j : Fin 3 → Fin d, (j 0 ≠ j 1 ∧ j 0 ≠ j 2 ∧ j 1 ≠ j 2) ∧
      (∀ i : Fin 3, lma_ClusterReachesRay ω (x i) (j i)) := by
  obtain ⟨f, hinj, hf⟩ := caa_axisAssignment ω x S h
  refine ⟨f, ⟨?_, ?_, ?_⟩,
    fun i => crr_clusterReachesRay_of_runsAlongAxis ω (x i) (f i) (hf i)⟩
  · intro he; exact absurd (hinj he) (by decide)
  · intro he; exact absurd (hinj he) (by decide)
  · intro he; exact absurd (hinj he) (by decide)


theorem caa_hall_of_full (hd : 3 ≤ d) (S : Fin 3 → Finset (Fin d))
    (hfull : ∀ i, S i = Finset.univ) :
    ∀ s : Finset (Fin 3), s.card ≤ (s.biUnion S).card := by
  intro s
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  · have hsub : s.biUnion S = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro y
      rw [Finset.mem_biUnion]
      exact ⟨a, ha, by rw [hfull a]; exact Finset.mem_univ y⟩
    rw [hsub, Finset.card_univ, Fintype.card_fin]
    calc s.card ≤ (Finset.univ : Finset (Fin 3)).card := Finset.card_le_univ s
      _ = 3 := by simp
      _ ≤ d := hd


theorem caa_hall_of_injective_singletons (a : Fin 3 → Fin d) (ha : Function.Injective a) :
    ∀ s : Finset (Fin 3), s.card ≤ (s.biUnion (fun i => ({a i} : Finset (Fin d)))).card := by
  intro s
  have he : s.biUnion (fun i => ({a i} : Finset (Fin d))) = s.image a := by
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_singleton, Finset.mem_image, eq_comm]
  rw [he, Finset.card_image_of_injective s ha]


theorem caa_attachData (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (S : Fin 3 → Finset (Fin d))
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
    tex_AttachData ω x₁ x₂ x₃ := by
  obtain ⟨j, _, hreach⟩ := caa_three_reachesRay ω ![x₁, x₂, x₃] S h
  exact lma_attachData_of_three_reachesRay ω x₁ x₂ x₃ (j 0) (j 1) (j 2)
    hcd12 hcd13 hcd23 (hreach 0) (hreach 1) (hreach 2)


theorem caa_threeClustersReachOrigin (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (S : Fin 3 → Finset (Fin d))
    (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂) (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
    (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
    (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
    ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) :=
  tex_threeClustersReachOrigin ω x₁ x₂ x₃ ⟨hcd12, hcd13, hcd23⟩
    (caa_attachData ω x₁ x₂ x₃ S hcd12 hcd13 hcd23 h)


end Percolation
end StatMech

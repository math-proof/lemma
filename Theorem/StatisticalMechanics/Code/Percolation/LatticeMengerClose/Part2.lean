/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.AxisAssignmentClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationFiniteEnergy.Part3
import Def.StatisticalMechanics.Code.Percolation.LatticeMengerClose
open MeasureTheory Set Finset
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem lmg_boxAttachData_of_assignment {n : ℕ}
    (h : lmg_BoxAxisAssignment d n) : tex_BoxAttachData d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨j₁, j₂, j₃, _, ha1, ha2, ha3⟩ :=
    h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact lmg_attachData ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 ha1 ha2 ha3


theorem lmg_disjointRouting_of_assignment {n : ℕ}
    (h : lmg_BoxAxisAssignment d n) : hrHD_DisjointRouting d n :=
  tex_disjointRouting_of_box (lmg_boxAttachData_of_assignment h)


theorem lmg_boxAttachData_of_candidates {n : ℕ}
    (h : caa_BoxRunsAlongCandidates d n) : tex_BoxAttachData d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨S, hcand⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact lmg_attachData_of_candidates ω x₁ x₂ x₃ S hcd12 hcd13 hcd23 hcand


theorem lmg_disjointRouting_of_candidates {n : ℕ}
    (h : caa_BoxRunsAlongCandidates d n) : hrHD_DisjointRouting d n :=
  tex_disjointRouting_of_box (lmg_boxAttachData_of_candidates h)


theorem lmg_axisAssignment_of_candidates (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (S : Fin 3 → Finset (Fin d))
    (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
    ∃ j₁ j₂ j₃ : Fin d, (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      crr_AxisAssignment ω x₁ j₁ ∧ crr_AxisAssignment ω x₂ j₂ ∧ crr_AxisAssignment ω x₃ j₃ := by
  obtain ⟨f, hinj, hf⟩ := caa_axisAssignment ω ![x₁, x₂, x₃] S h
  refine ⟨f 0, f 1, f 2, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro he; exact absurd (hinj he) (by decide)
  · intro he; exact absurd (hinj he) (by decide)
  · intro he; exact absurd (hinj he) (by decide)
  · simpa using hf 0
  · simpa using hf 1
  · simpa using hf 2


theorem lmg_boxAxisAssignment_of_candidates {n : ℕ}
    (h : caa_BoxRunsAlongCandidates d n) : lmg_BoxAxisAssignment d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  obtain ⟨S, hcand⟩ := h ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 hcd12 hcd13 hcd23
  exact lmg_axisAssignment_of_candidates ω x₁ x₂ x₃ S hcand


theorem lmg_axisAssignment_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} (hjd12 : j₁ ≠ j₂) (hjd13 : j₁ ≠ j₃) (hjd23 : j₂ ≠ j₃)
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
    (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      crr_AxisAssignment ω (hrHD_rayPt j₁ 1) j₁ ∧
      crr_AxisAssignment ω (hrHD_rayPt j₂ 1) j₂ ∧
      crr_AxisAssignment ω (hrHD_rayPt j₃ 1) j₃ :=
  ⟨⟨hjd12, hjd13, hjd23⟩, crr_runsAlongAxis_of_neighbour ω j₁ hi1,
    crr_runsAlongAxis_of_neighbour ω j₂ hi2, crr_runsAlongAxis_of_neighbour ω j₃ hi3⟩


theorem lmg_attachData_of_neighbour_witnesses (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d}
    (hcd12 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1))
    (hcd13 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hcd23 : cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
    (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
    tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) :=
  lmg_attachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) j₁ j₂ j₃
    hcd12 hcd13 hcd23
    (crr_runsAlongAxis_of_neighbour ω j₁ hi1) (crr_runsAlongAxis_of_neighbour ω j₂ hi2)
    (crr_runsAlongAxis_of_neighbour ω j₃ hi3)


theorem lmg_neighbour_witnesses_distinct {j₁ j₂ j₃ : Fin d}
    (hjd12 : j₁ ≠ j₂) (hjd13 : j₁ ≠ j₃) (hjd23 : j₂ ≠ j₃) :
    (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₂ 1 ∧
      (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₃ 1 ∧
      (hrHD_rayPt j₂ 1 : Site d) ≠ hrHD_rayPt j₃ 1 :=
  ⟨hrHD_rayPt_one_ne_of_ne hjd12, hrHD_rayPt_one_ne_of_ne hjd13, hrHD_rayPt_one_ne_of_ne hjd23⟩


theorem lmg_corridorVerts_nonempty (j : Fin d) (L : ℕ) :
    (lma_corridorVerts j L).Nonempty :=
  lma_corridorVerts_nonempty j L

end Percolation
end StatMech

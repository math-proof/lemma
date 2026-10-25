import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerClose.Part2
open MeasureTheory Set Finset StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[lmg_corridors_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_corridors_disjoint_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
  {L : ℕ}
-- given
  (hjd12 : j₁ ≠ j₂)
  (hjd13 : j₁ ≠ j₃)
  (hjd23 : j₂ ≠ j₃) :
-- imply
  (Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₂ L) ∧ Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₃ L) ∧ Disjoint (lma_corridorVerts j₂ L) (lma_corridorVerts j₃ L)) ∧ ((0 : Site d) ∉ lma_corridorVerts j₁ L ∧ (0 : Site d) ∉ lma_corridorVerts j₂ L ∧ (0 : Site d) ∉ lma_corridorVerts j₃ L) := by
-- proof
  apply StatMech.Percolation.lmg_corridors_disjoint hjd12 hjd13 hjd23 L

/--
[lmg_attachData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_attachData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h0 : crr_AxisAssignment ω x₁ j₁)
  (h1 : crr_AxisAssignment ω x₂ j₂)
  (h2 : crr_AxisAssignment ω x₃ j₃) :
-- imply
  tex_AttachData ω x₁ x₂ x₃ := by
-- proof
  apply StatMech.Percolation.lmg_attachData ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h0 h1 h2

/--
[lmg_attachData_of_candidates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_attachData_of_candidates_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {S : Fin 3 → Finset (Fin d)}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
-- imply
  tex_AttachData ω x₁ x₂ x₃ := by
-- proof
  apply StatMech.Percolation.lmg_attachData_of_candidates ω x₁ x₂ x₃ S hcd12 hcd13 hcd23 h

/--
[lmg_attachData_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_attachData_disjoint_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hjd12 : j₁ ≠ j₂)
  (hjd13 : j₁ ≠ j₃)
  (hjd23 : j₂ ≠ j₃)
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h0 : crr_AxisAssignment ω x₁ j₁)
  (h1 : crr_AxisAssignment ω x₂ j₂)
  (h2 : crr_AxisAssignment ω x₃ j₃) :
-- imply
  tex_AttachData ω x₁ x₂ x₃ ∧ ∀ L : ℕ, (Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₂ L) ∧ Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₃ L) ∧ Disjoint (lma_corridorVerts j₂ L) (lma_corridorVerts j₃ L)) ∧ ((0 : Site d) ∉ lma_corridorVerts j₁ L ∧ (0 : Site d) ∉ lma_corridorVerts j₂ L ∧ (0 : Site d) ∉ lma_corridorVerts j₃ L) := by
-- proof
  apply StatMech.Percolation.lmg_attachData_disjoint ω x₁ x₂ x₃ j₁ j₂ j₃ hjd12 hjd13 hjd23 hcd12 hcd13 hcd23 h0 h1 h2

/--
[lmg_threeClustersReachOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_threeClustersReachOrigin_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h0 : crr_AxisAssignment ω x₁ j₁)
  (h1 : crr_AxisAssignment ω x₂ j₂)
  (h2 : crr_AxisAssignment ω x₃ j₃) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Percolation.lmg_threeClustersReachOrigin ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h0 h1 h2

/--
[lmg_boxAttachData_of_assignment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_boxAttachData_of_assignment_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : lmg_BoxAxisAssignment d n) :
-- imply
  tex_BoxAttachData d n := by
-- proof
  apply StatMech.Percolation.lmg_boxAttachData_of_assignment h

/--
[lmg_disjointRouting_of_assignment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_disjointRouting_of_assignment_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : lmg_BoxAxisAssignment d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.lmg_disjointRouting_of_assignment h

/--
[lmg_boxAttachData_of_candidates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_boxAttachData_of_candidates_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : caa_BoxRunsAlongCandidates d n) :
-- imply
  tex_BoxAttachData d n := by
-- proof
  apply StatMech.Percolation.lmg_boxAttachData_of_candidates h

/--
[lmg_disjointRouting_of_candidates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_disjointRouting_of_candidates_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : caa_BoxRunsAlongCandidates d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Percolation.lmg_disjointRouting_of_candidates h

/--
[lmg_axisAssignment_of_candidates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_axisAssignment_of_candidates_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {S : Fin 3 → Finset (Fin d)}
-- given
  (h : caa_RunsAlongCandidates ω ![x₁, x₂, x₃] S) :
-- imply
  ∃ j₁ j₂ j₃ : Fin d, (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧ crr_AxisAssignment ω x₁ j₁ ∧ crr_AxisAssignment ω x₂ j₂ ∧ crr_AxisAssignment ω x₃ j₃ := by
-- proof
  apply StatMech.Percolation.lmg_axisAssignment_of_candidates ω x₁ x₂ x₃ S h

/--
[lmg_boxAxisAssignment_of_candidates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_boxAxisAssignment_of_candidates_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : caa_BoxRunsAlongCandidates d n) :
-- imply
  lmg_BoxAxisAssignment d n := by
-- proof
  apply StatMech.Percolation.lmg_boxAxisAssignment_of_candidates h

/--
[lmg_axisAssignment_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_axisAssignment_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hjd12 : j₁ ≠ j₂)
  (hjd13 : j₁ ≠ j₃)
  (hjd23 : j₂ ≠ j₃)
  (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
-- imply
  (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧ crr_AxisAssignment ω (hrHD_rayPt j₁ 1) j₁ ∧ crr_AxisAssignment ω (hrHD_rayPt j₂ 1) j₂ ∧ crr_AxisAssignment ω (hrHD_rayPt j₃ 1) j₃ := by
-- proof
  apply StatMech.Percolation.lmg_axisAssignment_of_neighbour_witnesses ω hjd12 hjd13 hjd23 hi1 hi2 hi3

/--
[lmg_attachData_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_attachData_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hcd12 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1))
  (hcd13 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
  (hcd23 : cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
  (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
-- imply
  tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) := by
-- proof
  apply StatMech.Percolation.lmg_attachData_of_neighbour_witnesses ω hcd12 hcd13 hcd23 hi1 hi2 hi3

/--
[lmg_neighbour_witnesses_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_neighbour_witnesses_distinct_eq
  {d : ℕ}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hjd12 : j₁ ≠ j₂)
  (hjd13 : j₁ ≠ j₃)
  (hjd23 : j₂ ≠ j₃) :
-- imply
  (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₂ 1 ∧ (hrHD_rayPt j₁ 1 : Site d) ≠ hrHD_rayPt j₃ 1 ∧ (hrHD_rayPt j₂ 1 : Site d) ≠ hrHD_rayPt j₃ 1 := by
-- proof
  apply StatMech.Percolation.lmg_neighbour_witnesses_distinct hjd12 hjd13 hjd23

/--
[lmg_corridorVerts_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerClose.lean)
-/
@[path]
private lemma lmg_corridorVerts_nonempty_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ} :
-- imply
  (lma_corridorVerts j L).Nonempty := by
-- proof
  apply StatMech.Percolation.lmg_corridorVerts_nonempty j L


-- created on 2026-10-23

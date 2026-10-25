/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteHighDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Def.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


lemma hrHD_mem_corridorEdges {j : Fin d} {L : ℕ} {t : ℕ} (ht : t < L) :
    s(hrHD_rayPt j (t : ℤ), hrHD_rayPt j ((t : ℤ) + 1)) ∈ hrHD_corridorEdges j L := by
  rw [hrHD_corridorEdges, Finset.mem_image]; exact ⟨t, Finset.mem_range.mpr ht, rfl⟩


lemma hrHD_origin_notMem_rayEdge (j : Fin d) (s : ℤ) (hs : 1 ≤ s) :
    (0 : Site d) ∉ s(hrHD_rayPt j s, hrHD_rayPt j (s + 1)) := by
  simp only [Sym2.mem_iff]
  push Not
  refine ⟨?_, ?_⟩
  · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega
  · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega


lemma hrHD_corridor_step_open (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) (s : ℕ)
    (h1 : 1 ≤ s) (hsL : s < L) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω))
      (hrHD_rayPt j (s : ℤ)) (hrHD_rayPt j ((s : ℤ) + 1)) := by
  refine ⟨hrHD_adj_rayPt j (s : ℤ), ?_⟩
  have hmem : s(hrHD_rayPt j (s : ℤ), hrHD_rayPt j ((s : ℤ) + 1)) ∈ hrHD_corridorEdges j L :=
    hrHD_mem_corridorEdges hsL
  have hno0 : (0 : Site d) ∉ s(hrHD_rayPt j (s : ℤ), hrHD_rayPt j ((s : ℤ) + 1)) :=
    hrHD_origin_notMem_rayEdge j (s : ℤ) (by exact_mod_cast h1)
  rw [removeSite_apply_of_notMem hno0, forceOpenFinset_of_mem hmem]


lemma hrHD_corridor_connected_one_to_L (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hL : 1 ≤ L) :
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j (L : ℤ)) := by
  set ω' := removeSite (0 : Site d) (forceOpenFinset (hrHD_corridorEdges j L) ω) with hω'
  suffices H : ∀ m : ℕ, 1 ≤ m → m ≤ L → Connected d ω' (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) by
    have := H L hL le_rfl; simpa using this
  intro m
  induction m with
  | zero => intro h; omega
  | succ p ih =>
    intro _ hpL
    rcases Nat.lt_or_ge 1 (p + 1) with hp | hp
    · have hp1 : 1 ≤ p := by omega
      have hppL : p < L := by omega
      have hstep : IsOpenEdge d ω' (hrHD_rayPt j (p : ℤ)) (hrHD_rayPt j ((p : ℤ) + 1)) :=
        hrHD_corridor_step_open ω j L p hp1 hppL
      have hrec : Connected d ω' (hrHD_rayPt j 1) (hrHD_rayPt j (p : ℤ)) := ih hp1 (by omega)
      have hgoal := hrec.trans hstep.connected
      have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [he] at hgoal
    · have hp1 : p + 1 = 1 := by omega
      rw [hp1]; simpa using connected_rfl


theorem hrHD_precursor_of_removeSite_conditions
    (ω : ConfigSpace (Sym2 (Site d))) (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧
      (cluster d (removeSite 0 ω) a₂).Infinite ∧
      (cluster d (removeSite 0 ω) a₃).Infinite)
    (hdist : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧
      cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧
      cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
    ω ∈ NeighborTrifPrecursor d a₁ a₂ a₃ := by
  refine ⟨hne, hadj, hinf, ?_, ?_, ?_⟩
  · intro hc; exact hdist.1 (cluster_eq_of_connected hc)
  · intro hc; exact hdist.2.1 (cluster_eq_of_connected hc)
  · intro hc; exact hdist.2.2 (cluster_eq_of_connected hc)


theorem hrHD_measurableSet_neighborTrifPrecursor (a₁ a₂ a₃ : Site d) :
    MeasurableSet (NeighborTrifPrecursor d a₁ a₂ a₃) := by
  classical
  have hcl : ∀ x : Site d, MeasurableSet
      {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite 0 ω) x).Infinite} := by
    intro x
    have h : {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite 0 ω) x).Infinite}
        = (fun ω => removeSite (0 : Site d) ω) ⁻¹' {ω' | (cluster d ω' x).Infinite} := rfl
    rw [h]; exact (measurable_removeSite 0) (measurableSet_clusterInfinite x)
  by_cases hpred : (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
        (hypercubicLattice d).Adj 0 a₃)
  · have hset : NeighborTrifPrecursor d a₁ a₂ a₃
        = ({ω | (cluster d (removeSite 0 ω) a₁).Infinite} ∩
            {ω | (cluster d (removeSite 0 ω) a₂).Infinite} ∩
            {ω | (cluster d (removeSite 0 ω) a₃).Infinite}) ∩
          (({ω | Connected d (removeSite 0 ω) a₁ a₂}ᶜ) ∩
            ({ω | Connected d (removeSite 0 ω) a₁ a₃}ᶜ) ∩
            ({ω | Connected d (removeSite 0 ω) a₂ a₃}ᶜ)) := by
      ext ω
      simp only [NeighborTrifPrecursor, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff]
      constructor
      · rintro ⟨_, _, ⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h4, h5⟩, h6⟩⟩
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, ⟨⟨h4, h5⟩, h6⟩⟩; exact ⟨hpred.1, hpred.2, ⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩
    rw [hset]
    exact ((((hcl a₁).inter (hcl a₂)).inter (hcl a₃)).inter
      ((((measurableSet_connected_removeSite 0 a₁ a₂).compl).inter
        ((measurableSet_connected_removeSite 0 a₁ a₃).compl)).inter
        ((measurableSet_connected_removeSite 0 a₂ a₃).compl)))
  · have hempty : NeighborTrifPrecursor d a₁ a₂ a₃ = ∅ := by
      ext ω
      simp only [NeighborTrifPrecursor, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2, _, _⟩; exact hpred ⟨h1, h2⟩
    rw [hempty]; exact MeasurableSet.empty


end Percolation
end StatMech

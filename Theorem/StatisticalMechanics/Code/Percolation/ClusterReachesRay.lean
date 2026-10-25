/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ClusterReachesRay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem crr_infinite_reaches_far (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d ω x).Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d ω x y :=
  (cluster_infinite_iff ω x).mp hinf n


theorem crr_infinite_reaches_far_coord (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d ω x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y := by
  obtain ⟨y, hyb, hyc⟩ := crr_infinite_reaches_far ω x hinf n
  rw [mem_box] at hyb
  push Not at hyb
  obtain ⟨i, hi⟩ := hyb
  exact ⟨y, ⟨i, hi⟩, hyc⟩


theorem crr_removeSite_infinite_reaches_far (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    (hinf : (cluster d (removeSite 0 ω) x).Infinite) (n : ℕ) :
    ∃ y, y ∉ box d n ∧ Connected d (removeSite 0 ω) x y :=
  (cluster_infinite_iff (removeSite 0 ω) x).mp hinf n


theorem crr_axisOpen_connected_in (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hopen : ∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true)
    (m : ℕ) (hm : m ≤ L) :
    Connected d ω (hrHD_rayPt j 1) (hrHD_rayPt j ((m : ℤ) + 1)) := by
  induction m with
  | zero => simpa using connected_rfl
  | succ p ih =>
    have hpL : p < L := by omega
    have hadj := hrHD_adj_rayPt j ((p : ℤ) + 1)
    have he2 : ((p : ℤ) + 1 + 1) = ((p : ℤ) + 2) := by ring
    rw [he2] at hadj
    have hstep : IsOpenEdge d ω (hrHD_rayPt j ((p : ℤ) + 1)) (hrHD_rayPt j ((p : ℤ) + 2)) :=
      ⟨hadj, hopen p hpL⟩
    have hrec := ih (by omega)
    have hgoal := hrec.trans hstep.connected
    have he : ((p : ℤ) + 2) = (((p : ℕ) + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rwa [he] at hgoal


theorem crr_axisOpen_connected_removeSite (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (hopen : ∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true)
    (m : ℕ) (hm : m ≤ L) :
    Connected d (removeSite 0 ω) (hrHD_rayPt j 1) (hrHD_rayPt j ((m : ℤ) + 1)) := by
  induction m with
  | zero => simpa using connected_rfl
  | succ p ih =>
    have hpL : p < L := by omega
    have hadj := hrHD_adj_rayPt j ((p : ℤ) + 1)
    have he2 : ((p : ℤ) + 1 + 1) = ((p : ℤ) + 2) := by ring
    rw [he2] at hadj
    have hno0 : (0 : Site d) ∉ s(hrHD_rayPt j ((p : ℤ) + 1), hrHD_rayPt j ((p : ℤ) + 2)) := by
      simp only [Sym2.mem_iff]; push Not
      refine ⟨?_, ?_⟩
      · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega
      · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega
    have hcfg : (removeSite 0 ω) s(hrHD_rayPt j ((p : ℤ) + 1), hrHD_rayPt j ((p : ℤ) + 2)) = true := by
      rw [removeSite_apply_of_notMem hno0]; exact hopen p hpL
    have hstep : IsOpenEdge d (removeSite 0 ω) (hrHD_rayPt j ((p : ℤ) + 1)) (hrHD_rayPt j ((p : ℤ) + 2)) :=
      ⟨hadj, hcfg⟩
    have hrec := ih (by omega)
    have hgoal := hrec.trans hstep.connected
    have he : ((p : ℤ) + 2) = (((p : ℕ) + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rwa [he] at hgoal


theorem crr_corridor_internal (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) (j : Fin d) (L : ℕ)
    (hxe1 : Connected d ω x (hrHD_rayPt j 1))
    (hopen : ∀ t : ℕ, t < L → ω s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) = true) :
    ∀ e ∈ lma_corridorEdges j L, ∀ p, p ∈ e → p ∈ cluster d ω x := by
  intro e he p hp
  rw [lma_corridorEdges, Finset.mem_image] at he
  obtain ⟨t, ht, rfl⟩ := he
  rw [Finset.mem_range] at ht
  rw [Sym2.mem_iff] at hp
  rw [mem_cluster]
  rcases hp with rfl | rfl
  · have hc := crr_axisOpen_connected_in ω j L hopen t (by omega)
    exact hxe1.trans hc
  · have hc := crr_axisOpen_connected_in ω j L hopen (t + 1) (by omega)
    have he : (((t : ℕ) + 1 : ℕ) : ℤ) + 1 = ((t : ℤ) + 2) := by push_cast; ring
    rw [he] at hc
    exact hxe1.trans hc


end Percolation
end StatMech

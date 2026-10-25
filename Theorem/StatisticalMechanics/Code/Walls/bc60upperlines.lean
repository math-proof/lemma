/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc60upperlines.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc59corridors.Part3
import Def.StatisticalMechanics.Code.Walls.bc60upperlines
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation


theorem bc60_open (k : ℤ) {h : ℤ} (hh : 1 ≤ h) :
    bc60_upperLines s(bc57_pt k h, bc57_pt (k + 1) h) = true := by
  classical
  rw [bc60_upperLines, if_pos]; exact ⟨k, h, hh, rfl⟩


theorem bc60_removeSite_mono (G : Finset (Sym2 (Site 2))) :
    removeSite 0 bc60_upperLines ≤ removeSite 0 (forceOpenFinset G bc60_upperLines) := by
  intro e
  unfold removeSite
  by_cases h : (0 : Site 2) ∈ e
  · simp [h]
  · simp only [h, if_false]; exact forceOpenFinset_le G bc60_upperLines e


theorem bc60_connected_forceOpen {G : Finset (Sym2 (Site 2))} {x y : Site 2}
    (h : Connected 2 (removeSite 0 bc60_upperLines) x y) :
    Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) x y :=
  connected_mono (bc60_removeSite_mono G) h


theorem bc60_origin_eq : (0 : Site 2) = bc57_pt 0 0 := by
  funext i; fin_cases i <;> simp [bc57_pt]


theorem bc60_pt_eq_origin_iff {a b : ℤ} : bc57_pt a b = (0 : Site 2) ↔ a = 0 ∧ b = 0 := by
  rw [bc60_origin_eq]
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp only [bc57_pt_fst, bc57_pt_snd] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨ha, hb⟩; rw [ha, hb]


theorem bc60_open_edge_heights {u v : Site 2}
    (hopen : bc60_upperLines s(u, v) = true) : 1 ≤ u 1 ∧ 1 ≤ v 1 ∧ u 1 = v 1 := by
  classical
  rw [bc60_upperLines] at hopen
  by_cases hk : ∃ (k : ℤ) (h : ℤ), 1 ≤ h ∧ s(u, v) = s(bc57_pt k h, bc57_pt (k + 1) h)
  · obtain ⟨k, h, hh, hkeq⟩ := hk
    rw [Sym2.eq_iff] at hkeq
    rcases hkeq with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    · rw [hu', hv', bc57_pt_snd, bc57_pt_snd]; exact ⟨hh, hh, rfl⟩
    · rw [hu', hv', bc57_pt_snd, bc57_pt_snd]; exact ⟨hh, hh, rfl⟩
  · rw [if_neg hk] at hopen; exact absurd hopen (by decide)


theorem bc60_line1_reach_pos (j : ℕ) :
    Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt 0 1) (bc57_pt (j : ℤ) 1) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 1)
  | succ i ih =>
    have h0 : (0 : Site 2) ∉ s(bc57_pt (i : ℤ) 1, bc57_pt ((i : ℤ) + 1) 1) := by
      rw [Sym2.mem_iff]
      rintro (h | h) <;> exact absurd (bc60_pt_eq_origin_iff.mp h.symm).2 (by decide)
    have hopen : (removeSite 0 bc60_upperLines) s(bc57_pt (i : ℤ) 1, bc57_pt ((i : ℤ) + 1) 1) = true := by
      rw [removeSite_apply_of_notMem h0]; exact bc60_open (i : ℤ) (by norm_num)
    have step : Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt (i : ℤ) 1)
        (bc57_pt ((i : ℤ) + 1) 1) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (i : ℤ) 1, hopen⟩
    have hcast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step


theorem bc60_line1_reach_neg (j : ℕ) :
    Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt 0 1) (bc57_pt (-(j : ℤ)) 1) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 1)
  | succ i ih =>
    have hadj : (hypercubicLattice 2).Adj (bc57_pt (-((i : ℤ)) - 1) 1) (bc57_pt (-((i : ℤ)) - 1 + 1) 1) :=
      bc57_pt_adj _ 1
    have heq : (-((i : ℤ)) - 1 + 1) = -((i : ℤ)) := by ring
    have h0 : (0 : Site 2) ∉ s(bc57_pt (-((i : ℤ)) - 1) 1, bc57_pt (-((i : ℤ)) - 1 + 1) 1) := by
      rw [Sym2.mem_iff]
      rintro (h | h) <;> exact absurd (bc60_pt_eq_origin_iff.mp h.symm).2 (by decide)
    have hopen : (removeSite 0 bc60_upperLines) s(bc57_pt (-((i : ℤ)) - 1) 1, bc57_pt (-((i : ℤ)) - 1 + 1) 1) = true := by
      rw [removeSite_apply_of_notMem h0]; exact bc60_open (-((i : ℤ)) - 1) (by norm_num)
    have step0 := IsOpenEdge.connected (d := 2) ⟨hadj, hopen⟩
    rw [heq] at step0
    have step : Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt (-((i : ℤ))) 1)
        (bc57_pt (-((i : ℤ)) - 1) 1) := step0.symm
    have hcast : (-(((i + 1 : ℕ)) : ℤ)) = -((i : ℤ)) - 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step


theorem bc60_line1_connected_zero (m : ℤ) :
    Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt m 1) (bc57_pt 0 1) := by
  rcases le_or_gt 0 m with hm | hm
  · 
    have : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
    have h := bc60_line1_reach_pos m.toNat
    rw [this] at h
    exact h.symm
  · 
    have hpos : 0 ≤ -m := by omega
    have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg hpos
    have h := bc60_line1_reach_neg (-m).toNat
    rw [this] at h
    have hmm : -(-m) = m := by ring
    rw [hmm] at h
    exact h.symm


theorem bc60_line1_all_connected (m m' : ℤ) :
    Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt m 1) (bc57_pt m' 1) :=
  (bc60_line1_connected_zero m).trans (bc60_line1_connected_zero m').symm


theorem bc60_step_height_diff {ω : ConfigSpace (Sym2 (Site 2))} {u v : Site 2}
    (hadj : (openSubgraph 2 ω).Adj u v) :
    (u 1 - v 1).natAbs ≤ 1 := by
  have hlat : (hypercubicLattice 2).Adj u v := hadj.1
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  omega


theorem bc60_reach_height_one {ω : ConfigSpace (Sym2 (Site 2))} {u y : Site 2}
    (hu : u 1 ≤ 0) (hy : 1 ≤ y 1) (hconn : Connected 2 ω u y) :
    ∃ w : Site 2, w 1 = 1 ∧ Connected 2 ω u w := by
  obtain ⟨walk⟩ := hconn
  induction walk with
  | nil => exact absurd hy (by omega)
  | @cons a b c hab w' ih =>
    
    have hstep : (a 1 - b 1).natAbs ≤ 1 := bc60_step_height_diff hab
    have habConn : Connected 2 ω a b :=
      SimpleGraph.Adj.reachable (G := openSubgraph 2 ω) hab
    by_cases hb : 1 ≤ b 1
    · 
      have hb1 : b 1 = 1 := by omega
      exact ⟨b, hb1, habConn⟩
    · 
      have hble : b 1 ≤ 0 := by omega
      obtain ⟨w, hw1, hwconn⟩ := ih hble hy
      exact ⟨w, hw1, habConn.trans hwconn⟩


end StatMech.Walls

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PressureSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.PressureFull
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
open Finset Filter Topology


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


theorem psv_adj_unique_coord {x y : Site d}
    (h : (∑ i, (x i - y i).natAbs) = 1) :
    ∃ i : Fin d, (x i - y i).natAbs = 1 ∧ ∀ j, j ≠ i → x j = y j := by
  set f : Fin d → ℕ := fun i => (x i - y i).natAbs with hf
  have hsum : ∑ i, f i = 1 := h
  obtain ⟨i, hi⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; norm_num : ∑ i, f i ≠ 0)
  have hfi : f i = 1 := by
    have hle : f i ≤ ∑ j, f j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hsum] at hle
    have hpos : 1 ≤ f i := Nat.one_le_iff_ne_zero.mpr hi.2
    omega
  refine ⟨i, hfi, ?_⟩
  intro j hj
  have hzero : ∑ k ∈ Finset.univ \ {i}, f k = 0 := by
    have hsplit : ∑ k, f k = (∑ k ∈ Finset.univ \ {i}, f k) + f i :=
      Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i) f
    rw [hsum, hfi] at hsplit; omega
  have hjmem : j ∈ Finset.univ \ {i} := by
    rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ j, by simp [hj]⟩
  have hfj : f j = 0 := (Finset.sum_eq_zero_iff.mp hzero) j hjmem
  have : (x j - y j).natAbs = 0 := hfj
  omega


open Classical in


theorem psv_nbr_card_le (x : Site d) (T : Finset (Site d)) :
    (T.filter (fun y => (hypercubicLattice d).Adj x y)).card ≤ 2 * d := by
  set S : Finset (Site d) :=
    ((Finset.univ : Finset (Fin d)) ×ˢ ({-1, 1} : Finset ℤ)).image
      (fun p => Function.update x p.1 (x p.1 + p.2)) with hS
  have hsub : T.filter (fun y => (hypercubicLattice d).Adj x y) ⊆ S := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨_, hadj⟩ := hy
    rw [hypercubicLattice_adj] at hadj
    obtain ⟨i, hi1, hrest⟩ := psv_adj_unique_coord hadj
    rw [hS, Finset.mem_image]
    refine ⟨(i, y i - x i), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨Finset.mem_univ _, ?_⟩
      have : (x i - y i).natAbs = 1 := hi1
      rw [Finset.mem_insert, Finset.mem_singleton]; omega
    · funext k
      by_cases hk : k = i
      · subst hk; rw [Function.update_self]; ring
      · rw [Function.update_of_ne hk]; exact hrest k hk
  calc (T.filter (fun y => (hypercubicLattice d).Adj x y)).card
      ≤ S.card := Finset.card_le_card hsub
    _ ≤ ((Finset.univ : Finset (Fin d)) ×ˢ ({-1, 1} : Finset ℤ)).card := Finset.card_image_le
    _ = (Finset.univ : Finset (Fin d)).card * ({-1, 1} : Finset ℤ).card :=
        Finset.card_product _ _
    _ ≤ 2 * d := by
        rw [Finset.card_univ, Fintype.card_fin]
        have h2 : ({-1, 1} : Finset ℤ).card ≤ 2 :=
          le_trans (Finset.card_insert_le _ _) (by simp)
        calc d * ({-1, 1} : Finset ℤ).card ≤ d * 2 := Nat.mul_le_mul_left _ h2
          _ = 2 * d := by ring


theorem psv_volume_card (d n : ℕ) : (boxFinset d n).card = (2 * n + 1) ^ d := by
  have : boxFinset d n = boxSV_boxF d n := by rw [boxSV_boxF_eq_toFinset]; rfl
  rw [this, boxSV_card_boxF]

theorem psv_volume_card_real (d n : ℕ) :
    ((boxFinset d n).card : ℝ) = (2 * (n : ℝ) + 1) ^ d := by
  rw [psv_volume_card]; push_cast; ring


end Ising
end StatMech

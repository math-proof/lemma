/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BoxSurfaceVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
open Set Finset Filter Topology


namespace StatMech

namespace Lattice

theorem boxSV_fwd_adj {d : ℕ} (hd : 1 ≤ d) (x : Site d) :
    (hypercubicLattice d).Adj x (Function.update x ⟨0, hd⟩ (x ⟨0, hd⟩ + 1)) := by
  classical
  rw [hypercubicLattice_adj]
  rw [Finset.sum_eq_single (⟨0, hd⟩ : Fin d)]
  · simp [Function.update_self]
  · intro b _ hb; rw [Function.update_of_ne hb]; simp
  · intro h; exact absurd (Finset.mem_univ _) h


theorem boxSV_fwd_maps {d n : ℕ} (hd : 1 ≤ d) (x : Site d) (hx : x ∈ boxSV_fwdDom d n hd) :
    (x, Function.update x ⟨0, hd⟩ (x ⟨0, hd⟩ + 1)) ∈ boxSV_edgeF d n := by
  classical
  rw [boxSV_mem_edgeF]
  refine ⟨?_, ?_, boxSV_fwd_adj hd x⟩
  · rw [boxSV_fwdDom, Finset.mem_filter] at hx; exact hx.1
  · rw [boxSV_fwdDom, Finset.mem_filter, boxSV_mem_boxF] at hx
    rw [boxSV_mem_boxF]
    intro i
    dsimp only
    by_cases hi : i = ⟨0, hd⟩
    · subst hi; rw [Function.update_self]; exact hx.2
    · rw [Function.update_of_ne hi]; exact hx.1 i


theorem boxSV_card_fwdDom {d n : ℕ} (hd : 1 ≤ d) :
    (boxSV_fwdDom d n hd).card = (2 * n) * (2 * n + 1) ^ (d - 1) := by
  classical
  unfold boxSV_fwdDom boxSV_boxF
  have heq : ((Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n)).filter
      (fun x => x ⟨0, hd⟩ + 1 ∈ Finset.Icc (-(n : ℤ)) n))
      = Fintype.piFinset (fun i : Fin d =>
          if i = ⟨0, hd⟩ then Finset.Icc (-(n : ℤ)) (n - 1) else Finset.Icc (-(n : ℤ)) n) := by
    ext x
    rw [Finset.mem_filter, Fintype.mem_piFinset, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ i
      have hi1 := h1 i
      by_cases hi : i = ⟨0, hd⟩
      · subst hi; rw [if_pos rfl, Finset.mem_Icc]
        rw [Finset.mem_Icc] at hi1
        rw [Finset.mem_Icc] at h2; omega
      · rw [if_neg hi]; exact hi1
    · intro h
      constructor
      · intro i
        have := h i
        by_cases hi : i = ⟨0, hd⟩
        · subst hi; rw [if_pos rfl, Finset.mem_Icc] at this
          rw [Finset.mem_Icc]; omega
        · rw [if_neg hi] at this; exact this
      · have := h ⟨0, hd⟩; rw [if_pos rfl, Finset.mem_Icc] at this
        rw [Finset.mem_Icc]; omega
  rw [heq, Fintype.card_piFinset]
  have hcard : ∀ i : Fin d, (if i = (⟨0, hd⟩ : Fin d) then Finset.Icc (-(n : ℤ)) (n - 1)
        else Finset.Icc (-(n : ℤ)) n).card
      = (if i = (⟨0, hd⟩ : Fin d) then (2 * n) else (2 * n + 1)) := by
    intro i
    by_cases hi : i = ⟨0, hd⟩
    · rw [if_pos hi, if_pos hi, Int.card_Icc]; omega
    · rw [if_neg hi, if_neg hi, Int.card_Icc]; omega
  rw [Finset.prod_congr rfl (fun i _ => hcard i),
    ← Finset.mul_prod_erase Finset.univ
      (fun i => if i = (⟨0, hd⟩ : Fin d) then (2 * n) else (2 * n + 1))
      (Finset.mem_univ (⟨0, hd⟩ : Fin d)),
    if_pos rfl]
  congr 1
  rw [Finset.prod_congr rfl (fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi)]),
    Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]


theorem boxSV_edge_card_lower {d n : ℕ} (hd : 1 ≤ d) :
    (2 * n) * (2 * n + 1) ^ (d - 1) ≤ boxSV_edgeCard d n := by
  unfold boxSV_edgeCard
  rw [← boxSV_card_fwdDom hd]
  apply Finset.card_le_card_of_injOn
    (fun x => (x, Function.update x ⟨0, hd⟩ (x ⟨0, hd⟩ + 1)))
  · intro x hx; exact boxSV_fwd_maps hd x hx
  · intro x _ y _ hxy
    exact (Prod.ext_iff.mp hxy).1


theorem boxSV_pow_sub_pow_le (a b : ℝ) (ha : 0 ≤ b) (hab : b ≤ a) (d : ℕ) :
    a ^ d - b ^ d ≤ (a - b) * (d * a ^ (d - 1)) := by
  have key : a ^ d - b ^ d = (∑ i ∈ range d, a ^ i * b ^ (d - 1 - i)) * (a - b) :=
    (geom_sum₂_mul a b d).symm
  rw [key, mul_comm (a - b)]
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  calc (∑ i ∈ range d, a ^ i * b ^ (d - 1 - i)) ≤ ∑ _i ∈ range d, a ^ (d - 1) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [Finset.mem_range] at hi
            have hb0 : (0 : ℝ) ≤ a := le_trans ha hab
            calc a ^ i * b ^ (d - 1 - i) ≤ a ^ i * a ^ (d - 1 - i) := by
                  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hb0 i)
                  exact pow_le_pow_left₀ ha hab (d - 1 - i)
              _ = a ^ (i + (d - 1 - i)) := by rw [pow_add]
              _ = a ^ (d - 1) := by congr 1; omega
        _ = d * a ^ (d - 1) := by rw [Finset.sum_const, card_range]; ring


theorem boxSV_ratio_le (d n : ℕ) (hd : 1 ≤ d) (hn : 1 ≤ n) :
    (boxSV_boundaryCard d n : ℝ) / (boxSV_edgeCard d n : ℝ) ≤ (d : ℝ) / n := by
  set P : ℝ := (2 * (n : ℝ) + 1) ^ (d - 1) with hP
  have hP0 : 0 < P := by rw [hP]; positivity
  
  have hbR : (boxSV_boundaryCard d n : ℝ)
      = (2 * (n : ℝ) + 1) ^ d - (2 * (n : ℝ) - 1) ^ d := by
    rw [boxSV_boundary_card d n hn]
    have hle : (2 * n - 1) ^ d ≤ (2 * n + 1) ^ d := Nat.pow_le_pow_left (by omega) d
    rw [Nat.cast_sub hle]
    congr 1
    · push_cast; ring
    · have h1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
        have : (1 : ℕ) ≤ 2 * n := by omega
        rw [Nat.cast_sub this]; push_cast; ring
      rw [← h1]; push_cast; ring_nf
  
  have hbound : (boxSV_boundaryCard d n : ℝ) ≤ 2 * (d * P) := by
    rw [hbR]
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have := boxSV_pow_sub_pow_le (2 * (n : ℝ) + 1) (2 * (n : ℝ) - 1)
      (by linarith) (by linarith) d
    calc (2 * (n : ℝ) + 1) ^ d - (2 * (n : ℝ) - 1) ^ d
        ≤ ((2 * (n : ℝ) + 1) - (2 * (n : ℝ) - 1)) * (d * (2 * (n : ℝ) + 1) ^ (d - 1)) := this
      _ = 2 * (d * P) := by rw [hP]; ring
  
  have heR : (2 * (n : ℝ)) * P ≤ (boxSV_edgeCard d n : ℝ) := by
    rw [hP]
    calc (2 * (n : ℝ)) * (2 * (n : ℝ) + 1) ^ (d - 1)
        = (((2 * n) * (2 * n + 1) ^ (d - 1) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (boxSV_edgeCard d n : ℝ) := by exact_mod_cast boxSV_edge_card_lower hd
  have hedge0 : 0 < (boxSV_edgeCard d n : ℝ) := lt_of_lt_of_le (by positivity) heR
  rw [div_le_div_iff₀ hedge0 (by exact_mod_cast hn)]
  calc (boxSV_boundaryCard d n : ℝ) * n ≤ (2 * (d * P)) * n :=
        mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (d : ℝ) * (2 * n * P) := by ring
    _ ≤ (d : ℝ) * boxSV_edgeCard d n := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc 2 * (n : ℝ) * P = (2 * (n : ℝ)) * P := by ring
            _ ≤ (boxSV_edgeCard d n : ℝ) := heR


theorem boxSV_ratio_tendsto_zero (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => (boxSV_boundaryCard d n : ℝ) / (boxSV_edgeCard d n : ℝ))
      atTop (𝓝 0) := by
  have hd0 : Tendsto (fun n : ℕ => (d : ℝ) / n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (d : ℝ))).div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero'
    (Eventually.of_forall (fun n => by positivity)) ?_ hd0
  filter_upwards [eventually_ge_atTop 1] with n hn using boxSV_ratio_le d n hd hn


theorem boxSV_edge_card_tendsto_atTop (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => boxSV_edgeCard d n) atTop atTop := by
  have hle : ∀ n, 2 * n ≤ boxSV_edgeCard d n := by
    intro n
    calc 2 * n = (2 * n) * 1 := by ring
      _ ≤ (2 * n) * (2 * n + 1) ^ (d - 1) := by
            apply Nat.mul_le_mul_left
            exact Nat.one_le_pow _ _ (by omega)
      _ ≤ boxSV_edgeCard d n := boxSV_edge_card_lower hd
  apply Filter.tendsto_atTop_mono hle
  apply Filter.tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n (by norm_num : 0 < 2))
  exact tendsto_id

end Lattice
end StatMech

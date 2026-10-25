/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ContinuousRectangleCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Def.StatisticalMechanics.Code.FK.ContinuousRectangleCrossing.Part5
open Set SimpleGraph Topology
open scoped unitInterval


namespace StatMech

namespace ContinuousRectangleCrossing

open Lattice RSW.Box


theorem gridFloor_coord_nonneg {n : ℕ} {p : Fin 2 → ℝ}
    (hp : InUnitSquare p) (i : Fin 2) :
    0 ≤ gridFloor n p i := by
  rw [gridFloor, Int.floor_nonneg]
  exact mul_nonneg (Nat.cast_nonneg _) (hp i).1

theorem gridFloor_coord_le {n : ℕ} {p : Fin 2 → ℝ}
    (hp : InUnitSquare p) (i : Fin 2) :
    gridFloor n p i ≤ (n : ℤ) := by
  change ⌊(n : ℝ) * p i⌋ ≤ (n : ℤ)
  rw [Int.floor_le_iff]
  have := mul_le_mul_of_nonneg_left (hp i).2 (Nat.cast_nonneg n)
  norm_num at this ⊢
  linarith


theorem gridFloor_error {n : ℕ} (hn : 0 < n) (p : Fin 2 → ℝ) (i : Fin 2) :
    |gridEmbed n (gridFloor n p) i - p i| < 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlo : ((gridFloor n p i : ℤ) : ℝ) ≤ (n : ℝ) * p i := by
    exact Int.floor_le _
  have hhi : (n : ℝ) * p i < ((gridFloor n p i : ℤ) : ℝ) + 1 := by
    exact Int.lt_floor_add_one _
  have hpdiv : p i = ((n : ℝ) * p i) / n := by
    field_simp
  rw [abs_lt]
  simp only [gridEmbed]
  rw [hpdiv, ← sub_div]
  constructor
  · rw [← neg_div, div_lt_div_iff_of_pos_right hnR]
    linarith
  · rw [div_lt_div_iff_of_pos_right hnR]
    linarith

theorem abs_lt_of_mem_uIcc {a b t x e : ℝ} (ht : t ∈ Set.uIcc a b)
    (ha : |a - x| < e) (hb : |b - x| < e) : |t - x| < e := by
  rw [Set.mem_uIcc] at ht
  rw [abs_lt] at ha hb ⊢
  rcases ht with ht | ht <;> constructor <;> linarith

theorem div_mem_uIcc_of_int_mem {n : ℕ} (hn : 0 < n) {a b t : ℤ}
    (ht : t ∈ Set.uIcc a b) :
    (t : ℝ) / n ∈ Set.uIcc ((a : ℝ) / n) ((b : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Set.mem_uIcc] at ht ⊢
  rcases ht with ht | ht
  · left
    constructor
    · rw [div_le_div_iff_of_pos_right hnR]; exact_mod_cast ht.1
    · rw [div_le_div_iff_of_pos_right hnR]; exact_mod_cast ht.2
  · right
    constructor
    · rw [div_le_div_iff_of_pos_right hnR]; exact_mod_cast ht.1
    · rw [div_le_div_iff_of_pos_right hnR]; exact_mod_cast ht.2

theorem gridFloor_other_error {n : ℕ} (hn : 0 < n)
    {p q : Fin 2 → ℝ} {i : Fin 2}
    (hpq : |p i - q i| < 1 / (n : ℝ)) :
    |gridEmbed n (gridFloor n q) i - p i| < 3 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hq := gridFloor_error hn q i
  rw [abs_lt] at hpq hq
  rw [abs_lt]
  constructor <;> rw [div_eq_mul_inv] at hpq hq ⊢ <;>
    linarith [inv_pos.mpr hnR]


theorem gridConnector_near {n : ℕ} (hn : 0 < n)
    {p q : Fin 2 → ℝ}
    (hpq : dist p q < 1 / (n : ℝ))
    {z : Site 2} (hz : z ∈ (gridConnector (gridFloor n p) (gridFloor n q)).support) :
    dist (gridEmbed n z) p < 3 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have heps : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
  rw [dist_pi_lt_iff (by positivity)]
  intro i
  have hpqi : |p i - q i| < 1 / (n : ℝ) := by
    rw [dist_pi_lt_iff heps] at hpq
    simpa [Real.dist_eq] using hpq i
  have hpp (j : Fin 2) := gridFloor_error hn p j
  have hqq (j : Fin 2) := gridFloor_error hn q j
  rw [gridConnector_mem_support] at hz
  rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · fin_cases i
    · apply (abs_lt_of_mem_uIcc
          (a := ((gridFloor n p 0 : ℤ) : ℝ) / n)
          (b := ((gridFloor n q 0 : ℤ) : ℝ) / n)
          (t := (t : ℝ) / n) (x := p 0) (e := 3 / (n : ℝ)))
      · exact div_mem_uIcc_of_int_mem hn ht
      · simpa [gridEmbed] using (hpp 0).trans
          ((div_lt_div_iff_of_pos_right hnR).2 (by norm_num))
      · simpa [gridEmbed] using gridFloor_other_error hn hpqi
    · simpa [gridEmbed, Real.dist_eq] using (hpp 1).trans
        ((div_lt_div_iff_of_pos_right hnR).2 (by norm_num))
  · fin_cases i
    · simpa [gridEmbed, Real.dist_eq] using gridFloor_other_error hn hpqi
    · apply (abs_lt_of_mem_uIcc
          (a := ((gridFloor n p 1 : ℤ) : ℝ) / n)
          (b := ((gridFloor n q 1 : ℤ) : ℝ) / n)
          (t := (t : ℝ) / n) (x := p 1) (e := 3 / (n : ℝ)))
      · exact div_mem_uIcc_of_int_mem hn ht
      · simpa [gridEmbed] using (hpp 1).trans
          ((div_lt_div_iff_of_pos_right hnR).2 (by norm_num))
      · simpa [gridEmbed] using gridFloor_other_error hn hpqi

theorem gridFloor_near {n : ℕ} (hn : 0 < n) (p : Fin 2 → ℝ) :
    dist (gridEmbed n (gridFloor n p)) p < 3 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [dist_pi_lt_iff (by positivity)]
  intro i
  simpa [Real.dist_eq] using (gridFloor_error hn p i).trans
    ((div_lt_div_iff_of_pos_right hnR).2 (by norm_num))

theorem coord_bounds_of_mem_uIcc {a b t lo hi : ℤ}
    (ht : t ∈ Set.uIcc a b) (ha0 : lo ≤ a) (ha1 : a ≤ hi)
    (hb0 : lo ≤ b) (hb1 : b ≤ hi) : lo ≤ t ∧ t ≤ hi := by
  rw [Set.mem_uIcc] at ht
  rcases ht with ht | ht <;> omega

theorem gridConnector_mem_rect {n : ℕ} {x y z : Site 2}
    (hx : x ∈ rect 0 (n : ℤ) 0 (n : ℤ))
    (hy : y ∈ rect 0 (n : ℤ) 0 (n : ℤ))
    (hz : z ∈ (gridConnector x y).support) :
    z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
  rw [mem_rect] at hx hy ⊢
  rw [gridConnector_mem_support] at hz
  rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
  · have hb := coord_bounds_of_mem_uIcc ht hx.1 hx.2.1 hy.1 hy.2.1
    simpa using ⟨hb.1, hb.2, hx.2.2.1, hx.2.2.2⟩
  · have hb := coord_bounds_of_mem_uIcc ht hx.2.2.1 hx.2.2.2 hy.2.2.1 hy.2.2.2
    simpa using ⟨hy.1, hy.2.1, hb.1, hb.2⟩

theorem gridWalk_mem_rect {n N : ℕ} {g : ℕ → Site 2}
    (hg : ∀ k ≤ N, g k ∈ rect 0 (n : ℤ) 0 (n : ℤ))
    {z : Site 2} (hz : z ∈ (gridWalk g N).support) :
    z ∈ rect 0 (n : ℤ) 0 (n : ℤ) := by
  rcases gridWalk_mem_support_cases g N z hz with rfl | ⟨k, hk, hzk⟩
  · exact hg 0 (Nat.zero_le _)
  · exact gridConnector_mem_rect (hg k hk.le) (hg (k + 1) hk) hzk


end ContinuousRectangleCrossing
end StatMech

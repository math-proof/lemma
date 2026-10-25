/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CoeffMatch
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part3


namespace StatMech.Onsager

open StatMech.Ising


theorem ons_X_eq_sector_sum (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_X (onsTorusGraph L) x =
      ons_sector00 L x + ons_sector10 L x + ons_sector01 L x + ons_sector11 L x := by
  rw [ons_X_eq_sum_sectorWeight]
  simp [ons_sector00, ons_sector10, ons_sector01, ons_sector11, Fin.sum_univ_two,
    Fintype.sum_prod_type]
  ring


theorem ons_two_mul_X_eq_spin_sum (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    2 * ons_X (onsTorusGraph L) x =
      ons_spin00 L x + ons_spin10 L x + ons_spin01 L x - ons_spin11 L x := by
  rw [ons_X_eq_sector_sum]
  unfold ons_spin00 ons_spin10 ons_spin01 ons_spin11
  ring

theorem ons_sectorWeight_nonneg (L : ℕ) [Fact (2 < L)] {x : ℝ} (hx : 0 ≤ x)
    (h : Fin 2 × Fin 2) : 0 ≤ ons_sectorWeight L x h := by
  unfold ons_sectorWeight
  positivity

theorem ons_sectorWeight_zero (L : ℕ) [Fact (2 < L)] (h : Fin 2 × Fin 2) :
    ons_sectorWeight L 0 h = if h = (0, 0) then 1 else 0 := by
  classical
  unfold ons_sectorWeight
  by_cases hh : h = (0, 0)
  · subst h
    rw [if_pos rfl]
    rw [Finset.sum_eq_single (∅ : Finset (Sym2 (ZMod L × ZMod L)))]
    · simp
    · intro F hF hFne
      have hcard : F.card ≠ 0 := by simpa [Finset.card_eq_zero] using hFne
      simp [hcard]
    · simp [evenSubgraphs, IsEvenSubgraph, incCount, ons_evenHomology]
  · rw [if_neg hh]
    apply Finset.sum_eq_zero
    intro F hF
    by_cases hFe : F = ∅
    · subst F
      simp [ons_evenHomology] at hF
      exact absurd hF.2.symm hh
    · have hcard : F.card ≠ 0 := by simpa [Finset.card_eq_zero] using hFe
      simp [hcard]


theorem ons_abs_spin_le_X (L : ℕ) [Fact (2 < L)] {x : ℝ} (hx : 0 ≤ x) :
    |ons_spin00 L x| ≤ ons_X (onsTorusGraph L) x ∧
    |ons_spin10 L x| ≤ ons_X (onsTorusGraph L) x ∧
    |ons_spin01 L x| ≤ ons_X (onsTorusGraph L) x ∧
    |ons_spin11 L x| ≤ ons_X (onsTorusGraph L) x := by
  have h00 := ons_sectorWeight_nonneg L hx ((0, 0) : Fin 2 × Fin 2)
  have h10 := ons_sectorWeight_nonneg L hx ((1, 0) : Fin 2 × Fin 2)
  have h01 := ons_sectorWeight_nonneg L hx ((0, 1) : Fin 2 × Fin 2)
  have h11 := ons_sectorWeight_nonneg L hx ((1, 1) : Fin 2 × Fin 2)
  rw [ons_X_eq_sector_sum]
  unfold ons_spin00 ons_spin10 ons_spin01 ons_spin11
  unfold ons_sector00 ons_sector10 ons_sector01 ons_sector11 at *
  constructor
  · rw [abs_le]
    constructor <;> linarith
  constructor
  · rw [abs_le]
    constructor <;> linarith
  constructor <;> rw [abs_le] <;> constructor <;> linarith


theorem ons_two_mul_X_le_sum_abs_spin (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    2 * ons_X (onsTorusGraph L) x ≤
      |ons_spin00 L x| + |ons_spin10 L x| + |ons_spin01 L x| + |ons_spin11 L x| := by
  rw [ons_two_mul_X_eq_spin_sum]
  linarith [le_abs_self (ons_spin00 L x), le_abs_self (ons_spin10 L x),
    le_abs_self (ons_spin01 L x), neg_le_abs (ons_spin11 L x)]

end StatMech.Onsager

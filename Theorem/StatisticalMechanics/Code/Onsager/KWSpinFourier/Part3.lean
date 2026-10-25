/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWSpinFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
import Def.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part3


namespace StatMech.Onsager

theorem ons_spinPhase_ne_zero (L : ℕ) (a : Fin 2) : ons_spinPhase L a ≠ 0 :=
  Complex.exp_ne_zero _

theorem ons_spinPhase_pow_side (L : ℕ) [NeZero L] (a : Fin 2) :
    ons_spinPhase L a ^ L = (-1 : ℂ) ^ a.val := by
  unfold ons_spinPhase
  rw [← Complex.exp_nat_mul]
  have ha : a.val = 0 ∨ a.val = 1 := by omega
  rcases ha with ha | ha
  · rw [ha]
    simp
  · rw [ha]
    norm_num only [Nat.cast_one, mul_one, one_mul]
    have harg : ((L : ℕ) : ℂ) *
        (Complex.I * (((Real.pi / L : ℝ)) : ℂ)) =
        (Real.pi : ℂ) * Complex.I := by
      have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
      push_cast
      field_simp [hL]
    rw [harg, Complex.exp_pi_mul_I]

theorem ons_spinPhase_mul_spaceRoot_pow (L m : ℕ) (a : Fin 2) :
    ons_spinPhase L a * ons_spaceRoot L ^ m =
      Complex.exp (Complex.I * ((2 * Real.pi * (m + (a.val : ℝ) / 2) / L : ℝ) : ℂ)) := by
  rw [ons_spaceRoot_pow]
  unfold ons_spinPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ons_spinPhase_spaceRoot_cos (L m : ℕ) (a : Fin 2) :
    ons_spinPhase L a * ons_spaceRoot L ^ m +
        (ons_spinPhase L a * ons_spaceRoot L ^ m)⁻¹ =
      2 * (Real.cos (2 * Real.pi * (m + (a.val : ℝ) / 2) / L) : ℂ) := by
  rw [ons_spinPhase_mul_spaceRoot_pow]
  have hinv :
      (Complex.exp (Complex.I *
        ((2 * Real.pi * (m + (a.val : ℝ) / 2) / L : ℝ) : ℂ)))⁻¹ =
      Complex.exp (-(Complex.I *
        ((2 * Real.pi * (m + (a.val : ℝ) / 2) / L : ℝ) : ℂ))) :=
    (Complex.exp_neg _).symm
  rw [hinv, Complex.ofReal_cos, Complex.two_cos]
  congr 2 <;> ring


theorem prod_zmod_prod_eq_prod_range (L : ℕ) [NeZero L] (F : ℕ → ℕ → ℂ) :
    (∏ j : ZMod L × ZMod L, F j.1.val j.2.val) =
      ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L, F i j := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  change (∏ j : Fin (q + 1) × Fin (q + 1), F j.1.val j.2.val) = _
  rw [Fintype.prod_prod_type]
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  have hiL : i < q + 1 := Finset.mem_range.mp hi
  simp only [hiL, dite_true]
  rw [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]


theorem ons_KWmatPhase_det_eq_spinDet (L : ℕ) [NeZero L] [Fact (1 < L)]
    (beta : ℝ) (a b : Fin 2) :
    (1 - ons_KWmatPhase L (Real.tanh beta : ℂ) ons_turnRoot
      (ons_spinPhase L a) (ons_spinPhase L b)).det =
        (ons_spinDet L beta a b : ℂ) := by
  rw [ons_KWmatPhase_det_eq_prod L (Real.tanh beta : ℂ) ons_turnRoot
    (ons_spinPhase L a) (ons_spinPhase L b) (ons_spaceRoot L)
    ons_turnRoot_sq (ons_spaceRoot_primitive L (NeZero.ne L))
    (ons_spinPhase_ne_zero L a) (ons_spinPhase_ne_zero L b)]
  have hfactor : ∀ i j : ℕ,
      ((1 + (Real.tanh beta : ℂ) ^ 2) ^ 2 -
        (Real.tanh beta : ℂ) * (1 - (Real.tanh beta : ℂ) ^ 2) *
          (ons_spinPhase L a * ons_spaceRoot L ^ i +
            (ons_spinPhase L a * ons_spaceRoot L ^ i)⁻¹ +
            (ons_spinPhase L b * ons_spaceRoot L ^ j +
              (ons_spinPhase L b * ons_spaceRoot L ^ j)⁻¹))) =
        (ons_symbolDispersion beta
          (2 * Real.pi * (i + (a.val : ℝ) / 2) / L)
          (2 * Real.pi * (j + (b.val : ℝ) / 2) / L) : ℂ) := by
    intro i j
    rw [ons_spinPhase_spaceRoot_cos, ons_spinPhase_spaceRoot_cos]
    unfold ons_symbolDispersion
    norm_cast
    ring
  have hprod :
      (∏ j : ZMod L × ZMod L,
        ((1 + (Real.tanh beta : ℂ) ^ 2) ^ 2 -
          (Real.tanh beta : ℂ) * (1 - (Real.tanh beta : ℂ) ^ 2) *
            (ons_spinPhase L a * ons_spaceRoot L ^ j.1.val +
              (ons_spinPhase L a * ons_spaceRoot L ^ j.1.val)⁻¹ +
              (ons_spinPhase L b * ons_spaceRoot L ^ j.2.val +
                (ons_spinPhase L b * ons_spaceRoot L ^ j.2.val)⁻¹)))) =
      (∏ j : ZMod L × ZMod L,
        (ons_symbolDispersion beta
          (2 * Real.pi * (j.1.val + (a.val : ℝ) / 2) / L)
          (2 * Real.pi * (j.2.val + (b.val : ℝ) / 2) / L) : ℂ)) := by
    apply Finset.prod_congr rfl
    intro j _
    exact hfactor j.1.val j.2.val
  rw [hprod]
  change (∏ z : ZMod L × ZMod L,
      (fun i j : ℕ =>
        (ons_symbolDispersion beta
          (2 * Real.pi * ((i : ℝ) + (a.val : ℝ) / 2) / L)
          (2 * Real.pi * ((j : ℝ) + (b.val : ℝ) / 2) / L) : ℂ))
        z.1.val z.2.val) = _
  let F : ℕ → ℕ → ℂ := fun i j =>
    (ons_symbolDispersion beta
      (2 * Real.pi * ((i : ℝ) + (a.val : ℝ) / 2) / L)
      (2 * Real.pi * ((j : ℝ) + (b.val : ℝ) / 2) / L) : ℂ)
  have hre : (∏ z : ZMod L × ZMod L, F z.1.val z.2.val) =
      ∏ i ∈ Finset.range L, ∏ j ∈ Finset.range L, F i j :=
    prod_zmod_prod_eq_prod_range L F
  change (∏ z : ZMod L × ZMod L, F z.1.val z.2.val) = _
  rw [hre]
  simp [F, ons_spinDet]

end StatMech.Onsager

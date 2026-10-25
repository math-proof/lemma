/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.KWFourier
import Theorem.StatisticalMechanics.Code.Onsager.IntegrandLimit.Part2
import Def.StatisticalMechanics.Code.Onsager.KWDetLimit


namespace StatMech.Onsager

theorem ons_turnRoot_sq : ons_turnRoot ^ 2 = Complex.I := by
  unfold ons_turnRoot
  rw [← Complex.exp_nat_mul]
  have harg : ((2 : ℕ) : ℂ) * (Complex.I * ((Real.pi : ℂ) / 4)) =
      (Real.pi : ℂ) / 2 * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_pi_div_two_mul_I]

theorem ons_spaceRoot_primitive (L : ℕ) (hL : L ≠ 0) :
    IsPrimitiveRoot (ons_spaceRoot L) L := by
  simpa [ons_spaceRoot, mul_assoc, mul_comm, mul_left_comm] using
    Complex.isPrimitiveRoot_exp L hL

theorem ons_spaceRoot_pow (L m : ℕ) :
    ons_spaceRoot L ^ m =
      Complex.exp (Complex.I * ((2 * Real.pi * m / L : ℝ) : ℂ)) := by
  unfold ons_spaceRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  by_cases hL : (L : ℂ) = 0
  · rw [hL]
    simp
  · field_simp

theorem ons_spaceRoot_pow_add_inv (L m : ℕ) :
    ons_spaceRoot L ^ m + (ons_spaceRoot L ^ m)⁻¹ =
      2 * (Real.cos (2 * Real.pi * m / L) : ℂ) := by
  rw [ons_spaceRoot_pow]
  have hinv :
      (Complex.exp (Complex.I * (((2 * Real.pi * m / L : ℝ)) : ℂ)))⁻¹ =
        Complex.exp (-(Complex.I * (((2 * Real.pi * m / L : ℝ)) : ℂ))) :=
    (Complex.exp_neg _).symm
  rw [hinv, Complex.ofReal_cos, Complex.two_cos]
  congr 2 <;> ring


theorem ons_KWmat_det_eq_symbolProd (L : ℕ) [NeZero L] [Fact (1 < L)]
    (β : ℝ) :
    (1 - ons_KWmat L (Real.tanh β : ℂ) ons_turnRoot).det =
      ∏ j : ZMod L × ZMod L,
        (ons_symbolDispersion β
          (2 * Real.pi * j.1.val / L) (2 * Real.pi * j.2.val / L) : ℂ) := by
  rw [ons_KWmat_det_eq_prod L (Real.tanh β : ℂ) ons_turnRoot (ons_spaceRoot L)
    ons_turnRoot_sq (ons_spaceRoot_primitive L (NeZero.ne L))]
  apply Finset.prod_congr rfl
  intro j _
  rw [ons_spaceRoot_pow_add_inv L j.1.val, add_assoc,
    ons_spaceRoot_pow_add_inv L j.2.val]
  norm_cast
  unfold ons_symbolDispersion
  ring


theorem log_abs_ons_KWmat_det_eq_sum (L : ℕ) [NeZero L] [Fact (1 < L)]
    (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC) :
    Real.log ‖(1 - ons_KWmat L (Real.tanh β : ℂ) ons_turnRoot).det‖ =
      ∑ j : ZMod L × ZMod L,
        Real.log (ons_symbolDispersion β
          (2 * Real.pi * j.1.val / L) (2 * Real.pi * j.2.val / L)) := by
  rw [ons_KWmat_det_eq_symbolProd]
  have hpos : ∀ j : ZMod L × ZMod L,
      0 < ons_symbolDispersion β
        (2 * Real.pi * j.1.val / L) (2 * Real.pi * j.2.val / L) := by
    intro j
    exact ons_symbolDispersion_pos β hβ hcrit _ _
  rw [norm_prod]
  simp_rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _)]
  exact Real.log_prod (fun j _ => (ne_of_gt (hpos j)))


theorem sum_zmod_prod_eq_sum_range (L : ℕ) [NeZero L] (F : ℕ → ℕ → ℝ) :
    (∑ j : ZMod L × ZMod L, F j.1.val j.2.val) =
      ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, F i j := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne L)
  change (∑ j : Fin (q + 1) × Fin (q + 1), F j.1.val j.2.val) = _
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hiL : i < q + 1 := Finset.mem_range.mp hi
  simp only [hiL, dite_true]
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  simp [Finset.mem_range.mp hj]


theorem ons_KWdet_density_tendsto (β : ℝ) (hβ : 0 ≤ β) (hcrit : β ≠ ons_betaC) :
    Filter.Tendsto
      (fun L : ℕ => if h : 2 < L then
        letI : Fact (2 < L) := ⟨h⟩
        Real.log ‖(1 - ons_KWmat L (Real.tanh β : ℂ) ons_turnRoot).det‖ /
          (2 * (L : ℝ) ^ 2)
      else 0)
      Filter.atTop
      (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
  have ht := ons_symbolDispersion_density_tendsto β hβ hcrit
  refine ht.congr' (Filter.eventually_atTop.2 ⟨3, fun L hL => ?_⟩)
  have h2 : 2 < L := by omega
  dsimp only
  rw [dif_pos h2]
  letI : Fact (2 < L) := ⟨h2⟩
  haveI : NeZero L := ⟨by omega⟩
  haveI : Fact (1 < L) := ⟨by omega⟩
  rw [log_abs_ons_KWmat_det_eq_sum L β hβ hcrit]
  have hsum :
      (∑ j : ZMod L × ZMod L,
        Real.log (ons_symbolDispersion β
          (2 * Real.pi * j.1.val / L) (2 * Real.pi * j.2.val / L))) =
      ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        Real.log (ons_symbolDispersion β
          (2 * Real.pi * i / L) (2 * Real.pi * j / L)) :=
    sum_zmod_prod_eq_sum_range L (fun i j =>
      Real.log (ons_symbolDispersion β
        (2 * Real.pi * i / L) (2 * Real.pi * j / L)))
  rw [hsum]
  ring


end StatMech.Onsager

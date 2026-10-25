/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareGridConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Calculus.Taylor
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency


namespace StatMech.Universality

open Set

noncomputable section

theorem taylorWithinEval_three_eq_cubic
    (g : Real → Real) (s : Real) (hs : s ≠ 0)
    (hg : ContDiff Real 4 g) :
    taylorWithinEval g 3 (uIcc 0 s) 0 s = cubicTaylorPolynomial g s := by
  have hu : UniqueDiffOn Real (uIcc 0 s) :=
    uniqueDiffOn_Icc (by grind [uIcc])
  have hzero : (0 : Real) ∈ uIcc 0 s := left_mem_uIcc
  have hiter (j : Nat) (hj : j ≤ 4) :
      iteratedDerivWithin j g (uIcc 0 s) 0 = iteratedDeriv j g 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hg.contDiffAt.of_le (by exact_mod_cast hj)) hzero
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hiter, cubicTaylorPolynomial]
  ring

theorem cubicTaylor_remainder_le_of_fourthDeriv_bound
    (g : Real → Real) (s M : Real) (hs : s ≠ 0)
    (hg : ContDiff Real 4 g)
    (hM : ∀ t ∈ uIcc 0 s, |iteratedDeriv 4 g t| ≤ M) :
    |g s - cubicTaylorPolynomial g s| ≤ M * |s| ^ 4 / 24 := by
  obtain ⟨t, ht, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (x := s) (x₀ := 0) hs.symm
      (hg.contDiffOn.mono (by rintro x -; exact mem_univ x))
      (n := 3)
  rw [← taylorWithinEval_three_eq_cubic g s hs hg, hrem]
  rw [abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (hM t (Ioo_subset_Icc_self ht)) (pow_nonneg (abs_nonneg s) 4))
    (by norm_num)


theorem centralSecondDifference_remainder_le
    (g : Real → Real) (h M : Real)
    (hg : ContDiff Real 4 g)
    (hfourth : ∀ t, |iteratedDeriv 4 g t| ≤ M) :
    |(g h + g (-h) - 2 * g 0) - iteratedDeriv 2 g 0 * h ^ 2| ≤
      M * |h| ^ 4 / 12 := by
  by_cases hh : h = 0
  · simp [hh]
    ring
  have hpos := cubicTaylor_remainder_le_of_fourthDeriv_bound
    g h M hh hg (fun t _ ↦ hfourth t)
  have hneg := cubicTaylor_remainder_le_of_fourthDeriv_bound
    g (-h) M (neg_ne_zero.mpr hh) hg (fun t _ ↦ hfourth t)
  have hid :
      (g h + g (-h) - 2 * g 0) - iteratedDeriv 2 g 0 * h ^ 2 =
        (g h - cubicTaylorPolynomial g h) +
          (g (-h) - cubicTaylorPolynomial g (-h)) := by
    unfold cubicTaylorPolynomial
    ring
  rw [hid]
  calc
    |(g h - cubicTaylorPolynomial g h) +
        (g (-h) - cubicTaylorPolynomial g (-h))| ≤
      |g h - cubicTaylorPolynomial g h| +
        |g (-h) - cubicTaylorPolynomial g (-h)| := abs_add_le _ _
    _ ≤ M * |h| ^ 4 / 24 + M * |-h| ^ 4 / 24 :=
      add_le_add hpos hneg
    _ = M * |h| ^ 4 / 12 := by rw [abs_neg]; ring

end
end StatMech.Universality

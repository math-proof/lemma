/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalFourthOrder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareGridConsistency.Part4


namespace StatMech.Universality

open Set

noncomputable section

theorem taylorWithinEval_three_eq_cubic_of_contDiffAt
    (g : Real -> Real) (s : Real) (hs : s ≠ 0)
    (hg0 : ContDiffAt Real 4 g 0) :
    taylorWithinEval g 3 (uIcc 0 s) 0 s = cubicTaylorPolynomial g s := by
  have hu : UniqueDiffOn Real (uIcc 0 s) :=
    uniqueDiffOn_Icc (by grind [uIcc])
  have hzero : (0 : Real) ∈ uIcc 0 s := left_mem_uIcc
  have hiter (j : Nat) (hj : j <= 4) :
      iteratedDerivWithin j g (uIcc 0 s) 0 = iteratedDeriv j g 0 :=
    iteratedDerivWithin_eq_iteratedDeriv hu
      (hg0.of_le (by exact_mod_cast hj)) hzero
  rw [taylor_within_apply]
  norm_num [Finset.sum_range_succ, hiter, cubicTaylorPolynomial]
  ring


theorem cubicTaylor_remainder_le_of_contDiffOn
    (g : Real -> Real) (s M : Real) (hs : s ≠ 0)
    (hg0 : ContDiffAt Real 4 g 0)
    (hg : ContDiffOn Real 4 g (uIcc 0 s))
    (hM : forall t, t ∈ uIcc 0 s -> |iteratedDeriv 4 g t| <= M) :
    |g s - cubicTaylorPolynomial g s| <= M * |s| ^ 4 / 24 := by
  obtain ⟨t, ht, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (x := s) (x₀ := 0) hs.symm hg (n := 3)
  rw [<- taylorWithinEval_three_eq_cubic_of_contDiffAt g s hs hg0, hrem]
  rw [abs_div, abs_mul, abs_pow]
  norm_num
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (hM t (Ioo_subset_Icc_self ht)) (pow_nonneg (abs_nonneg s) 4))
    (by norm_num)


end
end StatMech.Universality

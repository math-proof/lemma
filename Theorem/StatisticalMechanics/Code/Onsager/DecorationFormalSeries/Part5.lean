module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Def.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators Finset

theorem ons_mvSeriesEval_coe
    {E : Type*} (p : MvPolynomial E ℂ) (weight : E → ℂ) :
    ons_mvSeriesEval (p : MvPowerSeries E ℂ) weight =
      MvPolynomial.eval weight p := by
  classical
  unfold ons_mvSeriesEval
  rw [tsum_eq_sum (s := p.support)]
  · rw [MvPolynomial.eval_eq]
    apply Finset.sum_congr rfl
    intro m hm
    rw [MvPolynomial.coeff_coe, Finsupp.prod]
  · intro m hm
    rw [MvPolynomial.coeff_coe]
    have hcoeff : p.coeff m = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hm
    rw [hcoeff, zero_mul]


end StatMech.Onsager

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangZeroFree.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangFieldAnalytic.Part3
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangComplexFieldObservableNumerator_analyticOnNhd
    (beta : ℝ) (f : ConfigSpace V → ℂ) :
    AnalyticOnNhd ℂ
      (leeYangComplexFieldObservableNumerator G beta f) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro h hh
  apply DifferentiableAt.differentiableWithinAt
  unfold leeYangComplexFieldObservableNumerator
  fun_prop

theorem leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) (f : ConfigSpace V → ℂ) :
    AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f)
      {h : ℂ | h.re ≠ 0} := by
  exact ((leeYangComplexFieldObservableNumerator_analyticOnNhd G beta f).mono
      (Set.subset_univ _)).div
    ((leeYangComplexFieldPartition_analyticOnNhd G beta).mono
      (Set.subset_univ _))
    (fun h hh =>
      leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero G hbeta hh)

theorem leeYangComplexFieldExpectation_analyticOnNhd_rightHalfPlane
    {beta : ℝ} (hbeta : 0 ≤ beta) (f : ConfigSpace V → ℂ) :
    AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f)
      {h : ℂ | 0 < h.re} := by
  apply (leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero
    G hbeta f).mono
  intro h hh
  exact ne_of_gt hh

theorem leeYangComplexFieldExpectation_analyticOnNhd_leftHalfPlane
    {beta : ℝ} (hbeta : 0 ≤ beta) (f : ConfigSpace V → ℂ) :
    AnalyticOnNhd ℂ (leeYangComplexFieldExpectation G beta f)
      {h : ℂ | h.re < 0} := by
  apply (leeYangComplexFieldExpectation_analyticOnNhd_re_ne_zero
    G hbeta f).mono
  intro h hh
  exact ne_of_lt hh

theorem leeYangComplexFieldObservableNumerator_ofReal
    (beta h : ℝ) (f : ConfigSpace V → ℝ) :
    leeYangComplexFieldObservableNumerator G beta (fun s => (f s : ℂ)) (h : ℂ) =
      ((∑ s : ConfigSpace V, f s * isingWeight G beta h s : ℝ) : ℂ) := by
  unfold leeYangComplexFieldObservableNumerator
  push_cast
  apply Finset.sum_congr rfl
  intro s hs
  unfold isingWeight hamiltonian
  rw [Complex.ofReal_exp, mul_assoc]
  congr 2
  push_cast
  ring

theorem leeYangComplexFieldExpectation_ofReal
    (beta h : ℝ) (f : ConfigSpace V → ℝ) :
    leeYangComplexFieldExpectation G beta (fun s => (f s : ℂ)) (h : ℂ) =
      (isingExpectation G beta h f : ℂ) := by
  rw [leeYangComplexFieldExpectation,
    leeYangComplexFieldObservableNumerator_ofReal,
    leeYangComplexFieldPartition_ofReal]
  have hreal :
      (∑ s : ConfigSpace V, f s * isingWeight G beta h s) /
          isingZ G beta h = isingExpectation G beta h f := by
    unfold isingExpectation isingProb
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro s hs
    ring
  exact_mod_cast hreal

end StatMech.FrontierA

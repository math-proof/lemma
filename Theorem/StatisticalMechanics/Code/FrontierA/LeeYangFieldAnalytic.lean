/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangFieldAnalytic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangZeroFree.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangFieldAnalytic
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangComplexFieldPartition_hasDerivAt
    (beta : ℝ) (h : ℂ) :
    HasDerivAt (leeYangComplexFieldPartition G beta)
      (leeYangComplexFieldMagnetizationNumerator G beta h) h := by
  unfold leeYangComplexFieldPartition
  unfold leeYangComplexFieldMagnetizationNumerator
  apply HasDerivAt.fun_sum
  intro s hs
  have hinner : HasDerivAt
      (fun y : ℂ =>
        (beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
          (beta : ℂ) * y * (∑ v : V, spin s v))
      ((beta : ℂ) * (∑ v : V, spin s v)) h := by
    convert ((hasDerivAt_const h
      ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e))).add
        (((hasDerivAt_id h).const_mul (beta : ℂ)).mul_const
          (∑ v : V, spin s v))) using 1
    · funext y
      simp only [Pi.add_apply, id_eq]
      push_cast
      rfl
    · simp only [zero_add, mul_one]
      push_cast
      rfl
  convert hinner.cexp using 1
  ring

theorem leeYangComplexFieldPartition_analyticOnNhd (beta : ℝ) :
    AnalyticOnNhd ℂ (leeYangComplexFieldPartition G beta) Set.univ := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_univ
  intro h hh
  exact (leeYangComplexFieldPartition_hasDerivAt G beta h).differentiableAt.differentiableWithinAt

theorem leeYangComplexFieldMagnetizationNumerator_eq_deriv
    (beta : ℝ) (h : ℂ) :
    leeYangComplexFieldMagnetizationNumerator G beta h =
      deriv (leeYangComplexFieldPartition G beta) h := by
  exact (leeYangComplexFieldPartition_hasDerivAt G beta h).deriv.symm

theorem leeYangComplexFieldMagnetizationNumerator_ofReal
    (beta h : ℝ) :
    leeYangComplexFieldMagnetizationNumerator G beta (h : ℂ) =
      ((beta * ∑ s : ConfigSpace V,
        (∑ v : V, spin s v) * isingWeight G beta h s : ℝ) : ℂ) := by
  unfold leeYangComplexFieldMagnetizationNumerator
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  unfold isingWeight hamiltonian
  rw [Complex.ofReal_exp]
  rw [mul_assoc]
  congr 2
  congr 1
  push_cast
  ring

theorem leeYang_fugacity_norm_ne_one_of_re_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : h.re ≠ 0) :
    ‖Complex.exp (-2 * (beta : ℂ) * h)‖ ≠ 1 := by
  rw [Complex.norm_exp]
  intro hexp
  rw [Real.exp_eq_one_iff] at hexp
  have hre : (-2 * (beta : ℂ) * h).re = -2 * beta * h.re := by
    norm_num [Complex.mul_re]
  rw [hre] at hexp
  apply hh
  nlinarith

theorem leeYangComplexFieldPartition_ne_zero_of_re_ne_zero
    {beta : ℝ} (hbeta : 0 < beta) {h : ℂ} (hh : h.re ≠ 0) :
    leeYangComplexFieldPartition G beta h ≠ 0 :=
  leeYangComplexFieldPartition_ne_zero G hbeta.le
    (leeYang_fugacity_norm_ne_one_of_re_ne_zero hbeta hh)

theorem leeYangComplexFieldPartition_zero_beta (h : ℂ) :
    leeYangComplexFieldPartition G 0 h = Fintype.card (ConfigSpace V) := by
  simp [leeYangComplexFieldPartition]

theorem leeYangComplexFieldPartition_ne_zero_of_nonneg_re_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℂ} (hh : h.re ≠ 0) :
    leeYangComplexFieldPartition G beta h ≠ 0 := by
  rcases hbeta.eq_or_lt with rfl | hbeta
  · rw [leeYangComplexFieldPartition_zero_beta]
    exact_mod_cast Fintype.card_ne_zero
  · exact leeYangComplexFieldPartition_ne_zero_of_re_ne_zero G hbeta hh

end StatMech.FrontierA

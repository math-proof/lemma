/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangZeroFree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part15
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.LogDeriv
import Def.StatisticalMechanics.Code.FrontierA.LeeYangZeroFree
open scoped BigOperators
open Finset Polynomial


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem leeYangComplexFieldPartition_ofReal (beta h : ℝ) :
    leeYangComplexFieldPartition G beta (h : ℂ) = (isingZ G beta h : ℂ) := by
  unfold leeYangComplexFieldPartition isingZ isingWeight hamiltonian
  change (∑ s : ConfigSpace V, Complex.exp
      ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
        (beta : ℂ) * (h : ℂ) * (∑ v : V, spin s v))) =
    (algebraMap ℝ ℂ) (∑ s : ConfigSpace V,
      Real.exp (-beta * (-(∑ e ∈ G.edgeFinset, bond s e) -
        h * ∑ v : V, spin s v)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  change Complex.exp
      ((beta : ℂ) * (∑ e ∈ G.edgeFinset, bond s e) +
        (beta : ℂ) * (h : ℂ) * (∑ v : V, spin s v)) =
    (Real.exp (-beta * (-(∑ e ∈ G.edgeFinset, bond s e) -
      h * ∑ v : V, spin s v)) : ℂ)
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem leeYangComplexFieldPartition_eq_fugacity (beta : ℝ) (h : ℂ) :
    (leeYangComplexPolynomial G beta).eval (Complex.exp (-2 * (beta : ℂ) * h)) =
      Complex.exp (-(beta : ℂ) * h * Fintype.card V) *
        leeYangComplexFieldPartition G beta h := by
  rw [eval_leeYangComplexPolynomial]
  unfold leeYangComplexFieldPartition
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Complex.exp_nat_mul]
  unfold zeroFieldInteractionWeight
  rw [Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  rw [sum_spin_eq_card_sub_two_mul_minusSpinCount s]
  congr 1
  push_cast
  ring

theorem leeYangComplexPolynomial_ne_zero_of_norm_ne_one
    {beta : ℝ} (hbeta : 0 ≤ beta) {z : ℂ} (hz : ‖z‖ ≠ 1) :
    (leeYangComplexPolynomial G beta).eval z ≠ 0 := by
  intro hroot
  exact hz (finiteGraph_hasLeeYangCircle G hbeta z hroot)

theorem leeYangComplexFieldPartition_ne_zero
    {beta : ℝ} (hbeta : 0 ≤ beta) {h : ℂ}
    (hfugacity : ‖Complex.exp (-2 * (beta : ℂ) * h)‖ ≠ 1) :
    leeYangComplexFieldPartition G beta h ≠ 0 := by
  intro hzero
  apply leeYangComplexPolynomial_ne_zero_of_norm_ne_one G hbeta hfugacity
  rw [leeYangComplexFieldPartition_eq_fugacity, hzero, mul_zero]


end StatMech.FrontierA

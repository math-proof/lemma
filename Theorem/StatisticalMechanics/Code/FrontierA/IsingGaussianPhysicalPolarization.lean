/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalPolarization
open Filter Finset Polynomial Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in
theorem finiteIsingWeightedSpinReal_line
    (positive direction : V -> Real) (r : Real) (s : ConfigSpace V) :
    finiteIsingWeightedSpinReal (positive + r • direction) s =
      finiteIsingWeightedSpinReal positive s +
        r * finiteIsingWeightedSpinReal direction s := by
  unfold finiteIsingWeightedSpinReal
  simp_rw [Pi.add_apply, Pi.smul_apply, add_mul, smul_eq_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring_nf

theorem finiteIsingWeightedRawMomentLinePolynomial_eval
    (beta : Real) (positive direction : V -> Real)
    (order : Nat) (r : Real) :
    (finiteIsingWeightedRawMomentLinePolynomial
      G beta positive direction order).eval r =
      finiteIsingWeightedRawMoment G beta
        (positive + r • direction) order := by
  unfold finiteIsingWeightedRawMomentLinePolynomial
    finiteIsingWeightedRawMoment
  rw [eval_mul, eval_C, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X]
  rw [div_eq_inv_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [finiteIsingWeightedSpinReal_line]

theorem finiteIsingWeightedRawMomentLinePolynomial_natDegree_le
    (beta : Real) (positive direction : V -> Real) (order : Nat) :
    (finiteIsingWeightedRawMomentLinePolynomial
      G beta positive direction order).natDegree <= order := by
  unfold finiteIsingWeightedRawMomentLinePolynomial
  refine Polynomial.natDegree_mul_le.trans ?_
  have hsum :
      (∑ s : ConfigSpace V, C (zeroFieldInteractionWeight G beta s) *
        (C (finiteIsingWeightedSpinReal positive s) +
          X * C (finiteIsingWeightedSpinReal direction s)) ^ order).natDegree <=
        order := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s _
    refine Polynomial.natDegree_mul_le.trans ?_
    have hlinear :
        (C (finiteIsingWeightedSpinReal positive s) +
          X * C (finiteIsingWeightedSpinReal direction s)).natDegree <= 1 :=
      (Polynomial.natDegree_add_le _ _).trans
        (max_le (by simp)
          ((Polynomial.natDegree_mul_le).trans (by simp)))
    have hpow := Polynomial.natDegree_pow_le_of_le order hlinear
    simpa using hpow
  simpa using hsum


end
end StatMech.FrontierA

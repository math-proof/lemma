/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalPolarization.Part2
open Filter Finset Polynomial Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem scalarCumulantLinePolynomial_succ
    (moments : Nat -> Real[X]) (n : Nat) :
    scalarCumulantLinePolynomial moments (n + 1) = moments (n + 1) -
      ∑ k : Fin n, C (n.choose k : Real) *
        scalarCumulantLinePolynomial moments (k + 1) * moments (n - k) := by
  rw [scalarCumulantLinePolynomial]

theorem scalarCumulantLinePolynomial_eval
    (moments : Nat -> Real[X]) (r : Real) :
    forall order,
      (scalarCumulantLinePolynomial moments order).eval r =
        scalarCumulantsOfMoments (fun m => (moments m).eval r) order := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simp [scalarCumulantLinePolynomial,
          scalarCumulantsOfMoments_zero]
      | succ n =>
          rw [scalarCumulantLinePolynomial_succ,
            scalarCumulantsOfMoments_succ, eval_sub, eval_finsetSum]
          apply congrArg (fun x => (moments (n + 1)).eval r - x)
          apply Finset.sum_congr rfl
          intro k _
          simp only [eval_mul, eval_C]
          rw [ih (k.val + 1) (by omega)]

theorem scalarCumulantLinePolynomial_natDegree_le
    (moments : Nat -> Real[X])
    (hmoments : forall order, (moments order).natDegree <= order) :
    forall order,
      (scalarCumulantLinePolynomial moments order).natDegree <= order := by
  intro order
  induction order using Nat.strong_induction_on with
  | h order ih =>
      cases order with
      | zero => simp [scalarCumulantLinePolynomial]
      | succ n =>
          rw [scalarCumulantLinePolynomial_succ]
          apply (Polynomial.natDegree_sub_le _ _).trans
          apply max_le (hmoments (n + 1))
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro k _
          refine Polynomial.natDegree_mul_le.trans ?_
          refine (Nat.add_le_add Polynomial.natDegree_mul_le
            (hmoments (n - k.val))).trans ?_
          rw [Polynomial.natDegree_C]
          have hcumulant := ih (k.val + 1) (by omega)
          omega


end
end StatMech.FrontierA

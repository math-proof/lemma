/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardCumulants.Part2
open Filter
open scoped BigOperators Complex Nat


namespace StatMech.FrontierA

noncomputable section

def newmanRootCumulantRepresentation_of_evenHadamardFactorizations
    (F : Nat → Complex → Complex)
    (hF : ∀ scale, EvenHadamardFactorization (F scale)) :
    NewmanRootCumulantRepresentation
      (fun scale order => hadamardScalarCumulant (F scale) order) where
  roots := fun scale => (hF scale).roots
  roots_nonneg := fun scale => (hF scale).roots_nonneg
  roots_summable := fun scale => (hF scale).roots_summable
  order_zero := fun scale => hadamardScalarCumulant_zero (F scale)
  odd_order := fun scale order horder =>
    (hF scale).hadamardScalarCumulant_odd order horder
  even_power_sum := fun scale m hm => by
    rw [(hF scale).abs_hadamardScalarCumulant_even m (by omega)]
    exact mul_le_mul_of_nonneg_right
      (two_factorial_pred_le_factorial m (by omega))
      (tsum_nonneg fun n => pow_nonneg ((hF scale).roots_nonneg n) m)
  fourth_mass := fun scale => by
    rw [(hF scale).hadamardScalarCumulant_four]
    have hsum : 0 ≤ ∑' n, (hF scale).roots n ^ 2 :=
      tsum_nonneg fun n => sq_nonneg ((hF scale).roots n)
    rw [abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 12),
      abs_of_nonneg hsum]
  variance_mass := fun scale => by
    rw [(hF scale).hadamardScalarCumulant_two]
    have hsum : 0 ≤ ∑' n, (hF scale).roots n :=
      tsum_nonneg (hF scale).roots_nonneg
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hsum)]
    linarith


end
end StatMech.FrontierA

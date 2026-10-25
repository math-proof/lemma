/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingPeriodicProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicProduct.Part2
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingPeriodicProduct
open scoped BigOperators


namespace StatMech.FrontierA

theorem prod_one_sub_quantumIsingPeriodicRoot
    (n : Nat) (hn : n ≠ 0) (z : Complex) :
    (∏ j ∈ Finset.range n, (1 - z * quantumIsingPeriodicRoot n j)) =
      1 - z ^ n := by
  let zeta : Complex := Complex.exp (2 * Real.pi * Complex.I / n)
  have hzeta : IsPrimitiveRoot zeta n := by
    simpa [zeta] using Complex.isPrimitiveRoot_exp n hn
  have hp := X_pow_sub_C_eq_prod hzeta (Nat.pos_of_ne_zero hn)
    (by rfl : z ^ n = z ^ n)
  apply_fun Polynomial.eval (1 : Complex) at hp
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, one_pow, Polynomial.eval_prod] at hp
  calc
    (∏ j ∈ Finset.range n, (1 - z * quantumIsingPeriodicRoot n j)) =
        ∏ j ∈ Finset.range n, (1 - zeta ^ j * z) := by
      apply Finset.prod_congr rfl
      intro j hj
      unfold quantumIsingPeriodicRoot
      dsimp [zeta]
      ring
    _ = 1 - z ^ n := hp.symm

end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingAntiperiodicProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.KummerExtension
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingAntiperiodicProduct
open scoped BigOperators


namespace StatMech.FrontierA

theorem antiperiodicPhase_pow {n : Nat} (hn : n ≠ 0) :
    Complex.exp (Real.pi * Complex.I / n) ^ n = -1 := by
  rw [← Complex.exp_nat_mul]
  have hnC : (n : Complex) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [show (n : Complex) * (Real.pi * Complex.I / (n : Complex)) =
      Real.pi * Complex.I by field_simp [hnC]]
  exact Complex.exp_pi_mul_I


theorem prod_one_sub_quantumIsingAntiperiodicRoot
    (n : Nat) (hn : n ≠ 0) (z : Complex) :
    (∏ j ∈ Finset.range n,
      (1 - z * quantumIsingAntiperiodicRoot n j)) = 1 + z ^ n := by
  let zeta : Complex := Complex.exp (2 * Real.pi * Complex.I / n)
  let eta : Complex := Complex.exp (Real.pi * Complex.I / n)
  have hzeta : IsPrimitiveRoot zeta n := by
    simpa [zeta] using Complex.isPrimitiveRoot_exp n hn
  have heta : eta ^ n = -1 := by
    simpa [eta] using antiperiodicPhase_pow hn
  have he : (z * eta) ^ n = -(z ^ n) := by
    rw [mul_pow, heta]
    ring
  have hp := X_pow_sub_C_eq_prod hzeta (Nat.pos_of_ne_zero hn) he
  apply_fun Polynomial.eval (1 : Complex) at hp
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, one_pow, Polynomial.eval_prod] at hp
  calc
    (∏ j ∈ Finset.range n,
      (1 - z * quantumIsingAntiperiodicRoot n j)) =
        ∏ j ∈ Finset.range n, (1 - zeta ^ j * (z * eta)) := by
      apply Finset.prod_congr rfl
      intro j hj
      unfold quantumIsingAntiperiodicRoot
      dsimp [zeta, eta]
      ring
    _ = 1 - -(z ^ n) := hp.symm
    _ = 1 + z ^ n := by ring

end StatMech.FrontierA

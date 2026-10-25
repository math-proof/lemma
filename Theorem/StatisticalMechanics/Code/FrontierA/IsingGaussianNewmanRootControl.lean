/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianNewmanRootControl.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanBridge.Part2
import Mathlib.Topology.Algebra.InfiniteSum.Real
open scoped BigOperators


namespace StatMech.FrontierA

theorem tsum_pow_le_sq_tsum_mul_tsum_pow
    (roots : Nat → Real) (m : Nat) (hm : 2 ≤ m)
    (hroots : ∀ i, 0 ≤ roots i) (hsum : Summable roots) :
    (∑' i, roots i ^ m) ≤
      (∑' i, roots i ^ 2) * (∑' i, roots i) ^ (m - 2) := by
  let total : Real := ∑' i, roots i
  have htotal : 0 ≤ total := tsum_nonneg hroots
  have hle (i : Nat) : roots i ≤ total := by
    exact hsum.le_tsum i fun j _ => hroots j
  have hsquare : Summable (fun i => roots i ^ 2) := by
    refine (hsum.mul_right total).of_nonneg_of_le
      (fun i => sq_nonneg (roots i)) ?_
    intro i
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (hle i) (hroots i)
  have hpower : Summable (fun i => roots i ^ m) := by
    refine (hsquare.mul_right (total ^ (m - 2))).of_nonneg_of_le
      (fun i => pow_nonneg (hroots i) m) ?_
    intro i
    have hm' : m = 2 + (m - 2) := by omega
    have hpow' : roots i ^ m = roots i ^ 2 * roots i ^ (m - 2) := by
      calc
        roots i ^ m = roots i ^ (2 + (m - 2)) :=
          congrArg (fun n => roots i ^ n) hm'
        _ = roots i ^ 2 * roots i ^ (m - 2) := pow_add _ _ _
    calc
      roots i ^ m = roots i ^ 2 * roots i ^ (m - 2) := hpow'
      _ ≤ roots i ^ 2 * total ^ (m - 2) :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hroots i) (hle i) (m - 2)) (sq_nonneg (roots i))
  calc
    (∑' i, roots i ^ m) ≤
        ∑' i, roots i ^ 2 * total ^ (m - 2) := by
      exact hpower.tsum_le_tsum (fun i => by
        have hm' : m = 2 + (m - 2) := by omega
        have hpow' : roots i ^ m = roots i ^ 2 * roots i ^ (m - 2) := by
          calc
            roots i ^ m = roots i ^ (2 + (m - 2)) :=
              congrArg (fun n => roots i ^ n) hm'
            _ = roots i ^ 2 * roots i ^ (m - 2) := pow_add _ _ _
        rw [hpow']
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hroots i) (hle i) (m - 2)) (sq_nonneg (roots i)))
        (hsquare.mul_right (total ^ (m - 2)))
    _ = (∑' i, roots i ^ 2) * total ^ (m - 2) :=
      hsquare.tsum_mul_right _


end StatMech.FrontierA

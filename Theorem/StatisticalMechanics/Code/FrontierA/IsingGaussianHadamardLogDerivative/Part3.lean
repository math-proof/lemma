/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedHadamardPrereq
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanRootControl.Part2
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part3
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem EvenHadamardFactorization.logDeriv_eq_tsum
    {F : Complex → Complex} (hF : EvenHadamardFactorization F)
    {z : Complex} (hz : z ∈ hadamardRootNeighborhood hF.roots) :
    logDeriv F z =
      ∑' n, 2 * (hF.roots n : Complex) * z /
        (1 + (hF.roots n : Complex) * z ^ 2) := by
  have hfun : (fun w => F w / F 0) = hadamardRootProduct hF.roots := by
    funext w
    exact hF.normalized_eq w
  have hlog := congrArg (fun f : Complex → Complex => logDeriv f z) hfun
  have hconst : (F 0)⁻¹ ≠ 0 := inv_ne_zero hF.value_zero_ne
  rw [show (fun w => F w / F 0) = (fun w => F w * (F 0)⁻¹) by
      funext w; simp [div_eq_mul_inv]] at hlog
  change logDeriv (fun w => F w * (F 0)⁻¹) z =
    logDeriv (hadamardRootProduct hF.roots) z at hlog
  rw [logDeriv_mul_const z (F 0)⁻¹ hconst] at hlog
  rw [hlog]
  exact logDeriv_hadamardRootProduct_eq_tsum
    hF.roots_nonneg hF.roots_summable hz

end
end StatMech.FrontierA

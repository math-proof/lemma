/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalParameter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalMomentum
open Filter Topology


namespace StatMech.FrontierA

noncomputable section

theorem hasDerivAt_real_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  convert h using 1
  · ext y
    simpa using Real.tanh_eq_sinh_div_cosh y
  · field_simp [hc]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]

@[fun_prop] theorem differentiable_real_tanh : Differentiable ℝ Real.tanh :=
  fun x => (hasDerivAt_real_tanh x).differentiableAt

end
end StatMech.FrontierA

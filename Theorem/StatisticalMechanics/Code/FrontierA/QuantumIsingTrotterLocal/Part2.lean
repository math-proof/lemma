/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingTrotterLocal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Def.StatisticalMechanics.Code.FrontierA.QuantumIsingTrotterLocal.Part2


namespace StatMech.FrontierA

theorem quantumIsingTrotterKernel_eq_verticalWeight
    (beta h : ℝ) (n : ℕ) (s t : Bool)
    (hpos : 0 < beta * h / (2 * n)) :
    quantumIsingTrotterKernel beta h n s t =
      Real.exp (-quantumIsingVerticalCoupling beta h n) *
        Real.exp
          (quantumIsingVerticalCoupling beta h n *
            (quantumIsingSpinSign s * quantumIsingSpinSign t)) := by
  by_cases hst : s = t
  · subst t
    simp only [quantumIsingTrotterKernel,
      quantumIsingSpinSign_mul_self, mul_one]
    rw [← Real.exp_add]
    simp
  · rw [quantumIsingTrotterKernel, if_neg hst,
      quantumIsingSpinSign_mul_eq_neg_one_of_ne hst]
    rw [← Real.exp_add]
    have hcoupling :
        -quantumIsingVerticalCoupling beta h n +
            quantumIsingVerticalCoupling beta h n * -1 =
          Real.log (beta * h / (2 * n)) := by
      simp [quantumIsingVerticalCoupling]
      ring
    rw [hcoupling, Real.exp_log hpos]

end StatMech.FrontierA

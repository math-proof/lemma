/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part5
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

theorem triangularIsingRaySymbolAbsBound_pos (J b : Real) :
    0 < triangularIsingRaySymbolAbsBound J b := by
  unfold triangularIsingRaySymbolAbsBound
  positivity

theorem triangularIsingSymbol_le_rayAbsBound (J b p q : Real) :
    triangularIsingSymbol b b (b * J) p q <=
      triangularIsingRaySymbolAbsBound J b := by
  have hcp := Real.abs_cos_le_one p
  have hcq := Real.abs_cos_le_one q
  have hcpq := Real.abs_cos_le_one (p + q)
  unfold triangularIsingSymbol triangularIsingRaySymbolAbsBound
  have hraw := le_trans (le_abs_self
    (Real.cosh (2 * b) * Real.cosh (2 * b) * Real.cosh (2 * (b * J)) +
      Real.sinh (2 * b) * Real.sinh (2 * b) * Real.sinh (2 * (b * J)) -
      (Real.sinh (2 * b) * Real.cos p + Real.sinh (2 * b) * Real.cos q +
        Real.sinh (2 * (b * J)) * Real.cos (p + q))))
    (abs_sub _ _)
  calc
    _ <= |Real.cosh (2 * b) * Real.cosh (2 * b) * Real.cosh (2 * (b * J)) +
        Real.sinh (2 * b) * Real.sinh (2 * b) * Real.sinh (2 * (b * J))| +
      |Real.sinh (2 * b) * Real.cos p + Real.sinh (2 * b) * Real.cos q +
        Real.sinh (2 * (b * J)) * Real.cos (p + q)| := hraw
    _ <= (|Real.cosh (2 * b)| ^ 2 * |Real.cosh (2 * (b * J))| +
          |Real.sinh (2 * b)| ^ 2 * |Real.sinh (2 * (b * J))|) +
        (2 * |Real.sinh (2 * b)| + |Real.sinh (2 * (b * J))|) := by
      calc
        _ <= (|Real.cosh (2 * b) * Real.cosh (2 * b) * Real.cosh (2 * (b * J))| +
              |Real.sinh (2 * b) * Real.sinh (2 * b) * Real.sinh (2 * (b * J))|) +
            ((|Real.sinh (2 * b) * Real.cos p| +
                |Real.sinh (2 * b) * Real.cos q|) +
              |Real.sinh (2 * (b * J)) * Real.cos (p + q)|) := by
          gcongr
          · exact abs_add_le _ _
          · calc
              |(Real.sinh (2 * b) * Real.cos p +
                    Real.sinh (2 * b) * Real.cos q) +
                  Real.sinh (2 * (b * J)) * Real.cos (p + q)| <=
                  |Real.sinh (2 * b) * Real.cos p +
                    Real.sinh (2 * b) * Real.cos q| +
                  |Real.sinh (2 * (b * J)) * Real.cos (p + q)| :=
                    abs_add_le _ _
              _ <= (|Real.sinh (2 * b) * Real.cos p| +
                    |Real.sinh (2 * b) * Real.cos q|) +
                  |Real.sinh (2 * (b * J)) * Real.cos (p + q)| :=
                    by
                      have hab := abs_add_le
                        (Real.sinh (2 * b) * Real.cos p)
                        (Real.sinh (2 * b) * Real.cos q)
                      linarith
        _ <= _ := by
          simp only [abs_mul]
          have hpM : |Real.sinh (2 * b)| * |Real.cos p| <=
              |Real.sinh (2 * b)| :=
            mul_le_of_le_one_right (abs_nonneg _) hcp
          have hqM : |Real.sinh (2 * b)| * |Real.cos q| <=
              |Real.sinh (2 * b)| :=
            mul_le_of_le_one_right (abs_nonneg _) hcq
          have hpqM : |Real.sinh (2 * (b * J))| * |Real.cos (p + q)| <=
              |Real.sinh (2 * (b * J))| :=
            mul_le_of_le_one_right (abs_nonneg _) hcpq
          ring_nf at hpM hqM hpqM ⊢
          nlinarith
    _ <= _ := by
      have harg : 2 * (b * J) = 2 * b * J := by ring
      rw [harg]
      linarith

end
end StatMech.FrontierA

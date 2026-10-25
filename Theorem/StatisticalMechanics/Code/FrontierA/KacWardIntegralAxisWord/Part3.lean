/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3


namespace StatMech.FrontierA

open StatMech.Onsager.BaseCase


theorem kwIntegralPolygonDirection_closed
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) :
    ∑ k, stepOf (kwIntegralPolygonDirection p k) = 0 := by
  rw [← kwIntegralPolygonWord_step_sum p]
  simp [kwIntegralPolygonDirection]

end StatMech.FrontierA

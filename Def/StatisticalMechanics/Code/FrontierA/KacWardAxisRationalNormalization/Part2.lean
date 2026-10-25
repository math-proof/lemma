/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisRationalNormalization


namespace StatMech.FrontierA

open Set

open scoped BigOperators


noncomputable def kwAxisRatData
    {n : ℕ} (vertex : Fin n → ℂ) (eps : ℝ) (heps : 0 < eps) :
    Fin n → ℚ × ℚ :=
  fun i ↦ (kwRatApprox eps heps (vertex i).re,
    kwRatApprox eps heps (vertex i).im)

end StatMech.FrontierA

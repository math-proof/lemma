/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3


namespace StatMech.FrontierA

open Set

open scoped BigOperators


noncomputable def kwRatApprox (eps : ℝ) (heps : 0 < eps) (x : ℝ) : ℚ :=
  Classical.choose (exists_rat_btwn (by linarith : x - eps < x + eps))

end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisRationalNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardAxisRationalNormalization


namespace StatMech.FrontierA

open Set

open scoped BigOperators


theorem kwRatApprox_spec (eps : ℝ) (heps : 0 < eps) (x : ℝ) :
    x - eps < (kwRatApprox eps heps x : ℝ) ∧
      (kwRatApprox eps heps x : ℝ) < x + eps :=
  Classical.choose_spec (exists_rat_btwn (by linarith : x - eps < x + eps))

theorem abs_kwRatApprox_sub_lt (eps : ℝ) (heps : 0 < eps) (x : ℝ) :
    |(kwRatApprox eps heps x : ℝ) - x| < eps := by
  rw [abs_lt]
  constructor <;> linarith [kwRatApprox_spec eps heps x]


end StatMech.FrontierA

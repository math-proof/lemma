/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.IsingSHolo.Part3


namespace StatMech.Universality

open Complex


theorem isingF_sHolo_relation (X : ℂ) :
    isingF 0 X + isingF 1 X = isingF 2 X + isingF 3 X := by
  show (X + X / (Real.sqrt 2 : ℂ)) + isingLambda ^ 2 * X / (Real.sqrt 2 : ℂ)
      = isingLambda⁻¹ * X / (Real.sqrt 2 : ℂ)
        + (isingLambda * X + isingLambda * X / (Real.sqrt 2 : ℂ))
  have hsne := isingSqrt2_ne
  rw [isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp
  ring


theorem isingF_case1_relation :
    isingF 0 0 + isingF 1 0 = isingF 2 0 + isingF 3 0 := by
  simp only [isingF]
  ring


end StatMech.Universality

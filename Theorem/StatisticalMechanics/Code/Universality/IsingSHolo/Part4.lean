/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingSHolo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.IsingSHolo.Part4


namespace StatMech.Universality

open Complex


namespace IsingMedialVertex

variable (D : IsingMedialVertex)


theorem sHolo_relation : D.edgeObs 0 + D.edgeObs 1 = D.edgeObs 2 + D.edgeObs 3 :=
  isingF_sHolo_relation D.X


theorem sHolo_sub_zero : D.edgeObs 0 + D.edgeObs 1 - D.edgeObs 2 - D.edgeObs 3 = 0 := by
  have h := D.sHolo_relation; linear_combination h


theorem contourCombination_zero :
    D.edgeObs 0 - D.edgeObs 1 + Complex.I * D.edgeObs 3 - Complex.I * D.edgeObs 2 = 0 := by
  show (D.X + D.X / (Real.sqrt 2 : ℂ)) - isingLambda ^ 2 * D.X / (Real.sqrt 2 : ℂ)
      + Complex.I * (isingLambda * D.X + isingLambda * D.X / (Real.sqrt 2 : ℂ))
      - Complex.I * (isingLambda⁻¹ * D.X / (Real.sqrt 2 : ℂ)) = 0
  have hsne := isingSqrt2_ne
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := isingSqrt2_sq
  rw [isingLambda_inv, isingLambda_sq, isingLambda_val]
  field_simp
  ring_nf
  linear_combination (D.X * (Real.sqrt 2 : ℂ) + 2 * D.X) * hI + (D.X - D.X * Complex.I) * hs

end IsingMedialVertex
end StatMech.Universality

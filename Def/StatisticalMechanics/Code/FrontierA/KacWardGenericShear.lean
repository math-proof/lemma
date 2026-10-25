/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGenericShear.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase.Part2


namespace StatMech.FrontierA

def kwShearX (t : ℝ) (z : ℂ) : ℂ :=
  (z.re + t * z.im) + z.im * Complex.I

def kwShearY (t : ℝ) (z : ℂ) : ℂ :=
  z.re + (z.im + t * z.re) * Complex.I

end StatMech.FrontierA

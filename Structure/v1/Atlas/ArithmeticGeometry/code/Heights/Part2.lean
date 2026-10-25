/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisPlaceHelper
import Def.v1.Atlas.ArithmeticGeometry.code.Heights.Part3


noncomputable section

open Height MvPolynomial

namespace AbsoluteHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Empty.Finite ι]

attribute [instance] TwoIsogenyData.instAddCommGroup

attribute [instance] TwoIsogenyData.instDescentTargetGroup

attribute [instance] TwoIsogenyData.instDescentTarget'Group

attribute [instance] TwoIsogenyData.descentMap_range_finite

attribute [instance] TwoIsogenyData.descentMap'_range_finite

structure IsWeilHeightOnCurve (h : W.toAffine.Point → ℝ) : Prop where
  doubling_bound : ∃ C : ℝ, ∀ P : W.toAffine.Point,
    |h ((2 : ℤ) • P) - 4 * h P| ≤ C
  height_nonneg_zero : 0 ≤ h 0
  northcott : ∀ B : ℝ, {P : W.toAffine.Point | h P ≤ B}.Finite

end AbsoluteHeight
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisPlaceHelper

@[expose] public section

noncomputable section

open Height MvPolynomial

namespace AbsoluteHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Empty.Finite ι]

def absoluteHeight (P : Projectivization K (ι → K)) : ℝ :=
  Projectivization.mulHeight P


def logHeight (P : Projectivization K (ι → K)) : ℝ :=
  Real.log (absoluteHeight P)

end AbsoluteHeight
end

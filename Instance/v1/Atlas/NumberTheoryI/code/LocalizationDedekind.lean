/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalizationDedekind.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.LocalizationDedekind


noncomputable section

set_option linter.unusedSectionVars false

variable (A : Type*) [CommRing A] [IsDomain A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

instance Int.isDedekindDomain : IsDedekindDomain ℤ :=
  inferInstance


instance Polynomial.isDedekindDomain (k : Type*) [Field k] :
    IsDedekindDomain (Polynomial k) :=
  inferInstance

end

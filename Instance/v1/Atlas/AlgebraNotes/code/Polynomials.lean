/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Polynomials.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.AlgebraNotes.code.Polynomials


namespace Polynomials

instance polynomialUFD (F : Type*) [Field F] : UniqueFactorizationMonoid (Polynomial F) :=
  inferInstance

end Polynomials

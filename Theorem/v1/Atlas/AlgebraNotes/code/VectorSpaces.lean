/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/VectorSpaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Module


namespace VectorSpaces

open Submodule

variable {ι : Type*} {R : Type*} {M : Type*}
  [Semiring R] [AddCommMonoid M] [Module R M]

end VectorSpaces

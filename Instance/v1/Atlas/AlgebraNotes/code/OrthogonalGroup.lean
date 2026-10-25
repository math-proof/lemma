/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/OrthogonalGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace OrthogonalGroup

open Matrix

variable {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R]

attribute [local instance] starRingOfComm

instance orthogonalGroup_group : Group (Matrix.orthogonalGroup n R) := inferInstance

end OrthogonalGroup

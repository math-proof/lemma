/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/EuclideanProjectionBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.EuclideanProjectionBound


namespace ProjectionTheory

/-- Number of dyadic scales `1 ≤ r ≤ R` used in the wave packet decomposition;
explicitly `⌊log₂ ⌈R⌉⌋ + 1`. -/
noncomputable def numDyadicScales (d : EuclideanProjectionData) : ℕ :=
  Nat.log 2 (Nat.ceil d.R) + 1

end ProjectionTheory

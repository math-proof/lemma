/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/DoubleCountingReal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.ProjectionTheory.code.DoubleCountingReal
open Finset BigOperators


namespace ProjectionTheory

/-- The dyadic incidence-count sum `∑_{1 ≤ r ≤ R, dyadic} N_X(r) · N_D(1/r)` appearing
on the right-hand side of the real-version double-counting theorem. -/
noncomputable def dyadicSum (setup : DoubleCountingRealSetup) : ℕ :=
  ∑ k ∈ dyadicExponentRange setup.R, setup.N_X (2 ^ k) * setup.N_D ((2 : ℝ) ^ k)⁻¹

end ProjectionTheory

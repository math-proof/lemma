/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
set_option autoImplicit false

open DifferentialFormSpace


/-- The symplectic capacity of a ball or cylinder of radius $r$, defined as $\pi r^2$. -/
noncomputable def symplCapacity (r : ℝ) : NNReal :=
  ⟨Real.pi * r ^ 2, mul_nonneg Real.pi_nonneg (sq_nonneg r)⟩



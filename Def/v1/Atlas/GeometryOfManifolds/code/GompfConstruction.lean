/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/GompfConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.LinearAlgebra.Orientation
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

set_option autoImplicit false

open scoped Manifold


noncomputable section

namespace Gompf

/-- Local model for a Lefschetz singularity: the holomorphic map $(z_1, z_2) \mapsto z_1^2 + z_2^2$. -/
def lefschetzLocalModel : ℂ × ℂ → ℂ := fun p => p.1 ^ 2 + p.2 ^ 2

end Gompf
end

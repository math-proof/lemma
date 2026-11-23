/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/NormalCurvature.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.DifferentialGeometry.code.Manifolds.Part6
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Manifolds

@[expose] public section

noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

def normalCurvature {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (X : Fin n → ℝ) : ℝ :=
  (X ⬝ᵥ (secondFundamentalForm patch x).mulVec X) /
  (X ⬝ᵥ (firstFundamentalForm patch x).mulVec X)

end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.HomologySequence


noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace LongExactCohomology

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- The cochain shape relates `n` to `n + 1`. -/
lemma up_rel (n : ℤ) : (ComplexShape.up ℤ).Rel n (n + 1) := rfl

end LongExactCohomology
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/AffineWeylBook.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.AffineCoxeter.SemidirectProduct
import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv.Part3
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TransitiveAlcovesHelper
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- The "normal direction" of an affine hyperplane: the 1-dimensional submodule
spanned by its normal vector. Two parallel hyperplanes share the same normal
direction. -/
def normalDirection (η : AffineHyperplane E) : Submodule ℝ E :=
  Submodule.span ℝ {η.normal}

end AffineReflectionGroup
end

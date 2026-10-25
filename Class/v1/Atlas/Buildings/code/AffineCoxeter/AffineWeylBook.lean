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
import Def.v1.Atlas.Buildings.code.AffineCoxeter.AffineWeylBook
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- An affine reflection group is `NegIdFree` if the linear-part group does not
contain the negation $-\mathrm{id}_E$. This rules out the "$\bar W = \{\pm 1\}$"
degeneracy that would obstruct faithfulness of $\bar W$ on normal directions. -/
class NegIdFree (W : AffineReflectionGroup E) : Prop where
  neg_id_not_mem : ∀ (wbar : E ≃ₗᵢ[ℝ] E), wbar ∈ W.LinearPartGroup →
    (∀ v : E, wbar v = -v) → False

end AffineReflectionGroup
end

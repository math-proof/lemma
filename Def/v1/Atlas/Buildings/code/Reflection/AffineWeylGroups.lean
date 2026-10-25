/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
import Theorem.v1.Atlas.Buildings.code.Reflection.WallSeparationCorollary
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set

set_option maxHeartbeats 800000


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The monoid homomorphism sending an affine isometry equivalence to its linear part. -/
def linearPartHom : (E ≃ᵃⁱ[ℝ] E) →* (E ≃ₗᵢ[ℝ] E) where
  toFun := AffineIsometryEquiv.linearIsometryEquiv
  map_one' := by ext; rfl
  map_mul' := fun _ _ => by ext; rfl

end

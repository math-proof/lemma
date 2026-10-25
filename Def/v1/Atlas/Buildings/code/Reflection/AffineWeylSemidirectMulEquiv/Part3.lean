/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylSemidirectMulEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.AffineWeylGroupConstruction
import Mathlib.GroupTheory.SemidirectProduct
import Theorem.v1.Atlas.Buildings.code.Reflection.AffineWeylSemidirectMulEquiv
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineWeylSemidirectData

variable (d : AffineWeylSemidirectData E)

/-- The promised group isomorphism $W_a ≃ Λ(\check Φ) ⋊ W$. -/
def affineWeyl_semidirect_equiv : ↥d.affineWeylSubgroup ≃* d.SemiType where
  toFun := d.toSemidirect
  invFun := Function.surjInv d.toSemidirect_surjective
  left_inv _ := d.toSemidirect_injective (Function.surjInv_eq d.toSemidirect_surjective _)
  right_inv s := Function.surjInv_eq d.toSemidirect_surjective s
  map_mul' := d.toSemidirect_mul

end AffineWeylSemidirectData

namespace AffineWeylGroup

variable (Wa : AffineWeylGroup E)

/-- The set of affine reflections of the affine Weyl group $W_a$. -/
def affineReflections : Set (E ≃ᵃⁱ[ℝ] E) :=
  {s | s ∈ Wa.reflGroup.group ∧
    ∃ η ∈ Wa.reflGroup.arrangement.hyperplanes,
      (∀ y ∈ η.carrier, s y = y) ∧ s * s = 1}

end AffineWeylGroup
end

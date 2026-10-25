/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HCBimoduleProjectives.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Lemma.Int.Any_EqUeaAction
import Mathlib.Algebra.Lie.Semisimple.Defs
import Abbrev.v1.Atlas.LieGroups.code.HCBimoduleProjectives


noncomputable section

universe u_R u_𝔤 u_mod

variable {R : Type u_R} [CommRing R]

variable {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]

structure IsInHCThetaOne (M : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  right_annihilated : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M.carrier),
    M.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) m = θ z • m

structure HCThetaOneHom (M₁ M₂ : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (hM₁ : IsInHCThetaOne M₁ θ) (hM₂ : IsInHCThetaOne M₂ θ) where
  toLinearMap : M₁.carrier →ₗ[R] M₂.carrier
  left_compat : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M₁.carrier),
    toLinearMap (M₁.leftAction u m) = M₂.leftAction u (toLinearMap m)
  right_compat : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : M₁.carrier),
    toLinearMap (M₁.rightAction u m) = M₂.rightAction u (toLinearMap m)

end

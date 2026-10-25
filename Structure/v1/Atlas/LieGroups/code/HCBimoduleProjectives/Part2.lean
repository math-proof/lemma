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
import Def.v1.Atlas.LieGroups.code.HCBimoduleProjectives


noncomputable section

universe u_R u_𝔤 u_mod

variable {R : Type u_R} [CommRing R]

variable {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]

structure IsInHCTheta (M : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  annihilated_by_power : ∃ n : ℕ,
    ∀ (zs : List (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      zs.length = n →
      ∀ (m : M.carrier), iteratedKerThetaRightAction M θ zs m = 0

end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryOII.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryO.Part3
import Lemma.Int.IsInQPlus0
import Lemma.Int.Surjective_Comp.of.Surjective
import Def.v1.Atlas.LieGroups.code.TensorHomAxiom
import Def.v1.Atlas.LieGroups.code.CategoryOII.Part2


noncomputable section

open Classical

universe uCatO

universe u_V u_M u_P

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

variable {N' : Type*} [AddCommGroup N'] [Module R' N']
    [LieRingModule L' N'] [LieModule R' L' N']

omit [LieAlgebra R' L'] [LieModule R' L' M₁] [LieModule R' L' M₂] [LieModule R' L' N'] in
@[simp] lemma prodLieModuleHom_apply
    (f₁ : M₁ →ₗ⁅R', L'⁆ N') (f₂ : M₂ →ₗ⁅R', L'⁆ N') (m : M₁ × M₂) :
    prodLieModuleHom f₁ f₂ m = f₁ m.1 + f₂ m.2 := rfl

end

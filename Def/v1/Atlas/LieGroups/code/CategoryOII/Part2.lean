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
import Instance.v1.Atlas.LieGroups.code.CategoryOII


noncomputable section

open Classical

universe uCatO

universe u_V u_M u_P

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

variable {N' : Type*} [AddCommGroup N'] [Module R' N']
    [LieRingModule L' N'] [LieModule R' L' N']

noncomputable def prodLieModuleHom
    (f₁ : M₁ →ₗ⁅R', L'⁆ N') (f₂ : M₂ →ₗ⁅R', L'⁆ N') :
    M₁ × M₂ →ₗ⁅R', L'⁆ N' where
  toFun m := f₁ m.1 + f₂ m.2
  map_add' m n := by simp [map_add, add_add_add_comm]
  map_smul' r m := by simp [map_smul, smul_add]
  map_lie' {x m} := by
    show f₁ ⁅x, m.1⁆ + f₂ ⁅x, m.2⁆ = ⁅x, f₁ m.1 + f₂ m.2⁆
    rw [lie_add, f₁.map_lie, f₂.map_lie]

end

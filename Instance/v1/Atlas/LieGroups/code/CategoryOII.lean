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
import Structure.v1.Atlas.LieGroups.code.CategoryOII


noncomputable section

open Classical

universe uCatO

universe u_V u_M u_P

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

noncomputable instance prodLieRingModule : LieRingModule L' (M₁ × M₂) where
  bracket x m := (⁅x, m.1⁆, ⁅x, m.2⁆)
  add_lie x y m := by ext <;> exact add_lie ..
  lie_add x m n := by ext <;> exact lie_add ..
  leibniz_lie x y m := by ext <;> [exact leibniz_lie x y m.1; exact leibniz_lie x y m.2]

noncomputable instance prodLieModule : LieModule R' L' (M₁ × M₂) where
  smul_lie r x m := by ext <;> exact smul_lie ..
  lie_smul r x m := by ext <;> exact lie_smul ..

end

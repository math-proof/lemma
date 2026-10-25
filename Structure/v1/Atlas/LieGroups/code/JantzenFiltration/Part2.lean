/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/JantzenFiltration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
import Lemma.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Def.v1.Atlas.LieGroups.code.JantzenFiltration


section JantzenFiltrationProps

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {Δ : TriangularDecomposition R 𝔤}

structure FormalCharacterData
    (M : Type u_mod') [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVM : IsVermaModule Δ M wt) where
  CharGroup : Type u_ch'
  [instACG : AddCommGroup CharGroup]
  chSub : LieSubmodule R 𝔤 M → CharGroup
  chVerma : (Δ.𝔥 →ₗ[R] R) → CharGroup
  ch_top : chSub ⊤ = chVerma wt
  ch_bot : chSub ⊥ = 0

end JantzenFiltrationProps

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


noncomputable section

universe u_mod u_ch

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

structure JantzenFiltrationData
    (V₀ : Type*) [AddCommGroup V₀] [Module R V₀] where
  level : ℕ → Submodule R V₀
  level_zero : level 0 = ⊤
  antitone : Antitone level
  iInf_eq_bot : ⨅ m, level m = ⊥

structure VermaJantzenFiltration
    {Δ : TriangularDecomposition R 𝔤}
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVM : IsVermaModule Δ M wt) where
  level : ℕ → LieSubmodule R 𝔤 M
  level_zero : level 0 = ⊤
  antitone : Antitone level
  iInf_eq_bot : ⨅ i, level i = ⊥
  level_one_is_maximal : level 1 ≠ ⊤ ∧
    (∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ level 1)

end

section JantzenFiltrationProps

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {Δ : TriangularDecomposition R 𝔤}

structure RootCorootData (rd : PositiveRootData Δ) where
  corootPairing : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R

end JantzenFiltrationProps

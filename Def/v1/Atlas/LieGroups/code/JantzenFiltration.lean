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
import Structure.v1.Atlas.LieGroups.code.JantzenFiltration


section JantzenFiltrationProps

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {Δ : TriangularDecomposition R 𝔤}

def RootCorootData.ofPositiveRootData (rd : PositiveRootData Δ) : RootCorootData rd :=
  ⟨rd.corootPairing⟩

def dotReflectedWeight {rd : PositiveRootData Δ}
    (wg : WeylGroupData Δ)
    (cd : RootCorootData rd)
    (lam : Δ.𝔥 →ₗ[R] R) (α : Δ.𝔥 →ₗ[R] R) :
    Δ.𝔥 →ₗ[R] R :=
  lam - cd.corootPairing (lam + wg.ρ) α • α

end JantzenFiltrationProps

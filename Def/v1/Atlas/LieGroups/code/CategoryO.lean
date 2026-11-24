module
public import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
public import Theorem.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
public import Theorem.Int.Any_All_Eq.of.LeKer_Ker.Surjective
public import Theorem.Int.IsIntegral
public import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
public import Instance.v1.Atlas.LieGroups.code.HilbertNoether
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def HasWeightDecomposition (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] : Prop :=
  ∀ m : M, ∃ (S : Finset (Δ.𝔥 →ₗ[R] R)) (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ),
    m = ∑ μ ∈ S, (v μ : M)

end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CategoryO.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.VermaModules.Part7
public import Theorem.Int.WeightSubspace.eq.ToSubmoduleWeightSpace
public import Theorem.Int.IsIntegral
public import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
public import Instance.v1.Atlas.LieGroups.code.HilbertNoether
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Def.v1.Atlas.LieGroups.code.CategoryO


public noncomputable section

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

structure IsCategoryO (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  finitely_generated : ∃ (S : Finset M), LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤
  weight_decomp : HasWeightDecomposition Δ M
  weight_bound : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
    ∀ μ ∈ weights Δ M, ∃ wt ∈ bds, rd.IsInQPlus (wt - μ)

end

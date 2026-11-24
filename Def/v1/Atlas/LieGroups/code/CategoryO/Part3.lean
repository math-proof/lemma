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
public import Structure.v1.Atlas.LieGroups.code.CategoryO.Part2


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

section CategoryOResults

variable {Δ : TriangularDecomposition R 𝔤}

variable {rd : PositiveRootData Δ}

variable {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

def rootsOfStabilizer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (x : Δ.𝔥 →ₗ[R] R) : Set (Δ.𝔥 →ₗ[R] R) :=
  {α | α ∈ rs.allRoots ∧ rs.reflection α ∈ WeylStabilizerModQ rd wg x}

def IsRootSubsystem
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Prop :=

  (∀ α ∈ S, α ∈ rs.allRoots) ∧

  ((0 : Δ.𝔥 →ₗ[R] R) ∉ S) ∧

  (∀ α ∈ S, -α ∈ S) ∧

  (∀ α ∈ S, ∀ β ∈ S, wg.dualAction (rs.reflection α) β ∈ S)

def corootsOf
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    (rs : RootSystemWithReflections rd wg)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Set Δ.𝔥 :=
  {h : Δ.𝔥 | ∃ α ∈ S, h = rs.coroot α}

end CategoryOResults
end

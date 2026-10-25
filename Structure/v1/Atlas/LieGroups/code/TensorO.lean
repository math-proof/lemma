/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TensorO.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Lemma.Int.WeightLE.of.BruhatLE
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Data.Multiset.Basic
universe v


noncomputable section

structure HasVermaFiltration
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (Δ_weights : Multiset (Δ.𝔥 →ₗ[R] R)) where
  length : ℕ
  filtration : Fin (length + 1) → LieSubmodule R 𝔤 M
  mono : ∀ i : Fin length, filtration ⟨i, by omega⟩ ≤ filtration ⟨i + 1, by omega⟩
  bot : filtration ⟨0, by omega⟩ = ⊥
  top : filtration ⟨length, Nat.lt_succ_iff.mpr (le_refl _)⟩ = ⊤
  quotient_weights : Fin length → (Δ.𝔥 →ₗ[R] R)
  weights_eq : (Finset.univ.val.map quotient_weights) = Δ_weights
  quotient_is_verma : ∀ i : Fin length,
    ∃ (Q : Type*) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q),
      Nonempty (IsVermaModule Δ Q (quotient_weights i))

structure CategoryOProperties
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) where
  noetherian : ∀ (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M],
    IsCategoryO Δ rd M →
    ∀ (chain : ℕ → LieSubmodule R 𝔤 M),
      (∀ n, chain n ≤ chain (n + 1)) →
      ∃ N, ∀ n, N ≤ n → chain n = chain N
  enough_projectives : ∀ (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M],
    IsCategoryO Δ rd M →
    ∃ (P : Type*) (_ : AddCommGroup P) (_ : Module R P)
      (_ : LieRingModule 𝔤 P) (_ : LieModule R 𝔤 P)
      (hPO : IsCategoryO Δ rd P),
      IsProjectiveInO rd P hPO ∧
      ∃ (f : P →ₗ⁅R, 𝔤⁆ M), Function.Surjective f
  hom_finiteDimensional : ∀ (P : Type*) [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P],
    ∀ (hPO : IsCategoryO Δ rd P),
    IsProjectiveInO rd P hPO →
    ∀ (M : Type*) [AddCommGroup M] [Module R M]
      [LieRingModule 𝔤 M] [LieModule R 𝔤 M],
    IsCategoryO Δ rd M →
    Module.Finite R (P →ₗ⁅R, 𝔤⁆ M)

end

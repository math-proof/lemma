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


noncomputable section

open Classical

universe uCatO

universe u_V u_M u_P

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def IsDominantWeightLE {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), w ∈ WeylStabilizerModQ rd wg lam →
    WeightLE rd lam (wg.dualAction w lam) → lam = wg.dualAction w lam

def IsDominantWeightBruhat {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), w ∈ WeylStabilizerModQ rd wg lam →
    BruhatLE rd lam (wg.dualAction w lam) → lam = wg.dualAction w lam

def NotNegIntCorootPairing
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, ¬ ∃ n : ℤ, n < 0 ∧ lam (rs.coroot α) = (n : R)

def IsIntegralDominantWeightBruhat
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ w : wg.W, w ∈ WeylStabilizerModQ rd wg lam → BruhatLE rd (wg.dualAction w lam) lam

def IsIntegralDominantWeightLE
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ w : wg.W, w ∈ WeylStabilizerModQ rd wg lam → WeightLE rd (wg.dualAction w lam) lam

def IsProjectiveInO {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (P : Type uCatO) [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hP : IsCategoryO Δ rd P) : Prop :=
  ∀ (M : Type uCatO) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_ : IsCategoryO Δ rd M),
  ∀ (N : Type uCatO) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (_ : IsCategoryO Δ rd N),
  ∀ (f : M →ₗ⁅R, 𝔤⁆ N) (_ : Function.Surjective f)
    (g : P →ₗ⁅R, 𝔤⁆ N),
    ∃ (h : P →ₗ⁅R, 𝔤⁆ M), ∀ p, f (h p) = g p

def IsInBlockO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (_wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  IsCategoryO Δ rd M ∧


  ∃ (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R),
    GeneralizedEigenspaceCenter M ueaAct chi = ⊤

end

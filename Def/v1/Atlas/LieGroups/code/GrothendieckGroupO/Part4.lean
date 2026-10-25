/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GrothendieckGroupO.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part7
import Lemma.Int.IsDirectSummand
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part9
import Structure.v1.Atlas.LieGroups.code.GrothendieckGroupO.Part3
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


noncomputable section

open scoped TensorProduct

open ProjectiveFunctors Classical

universe u

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

section Theorems

variable {Δ : TriangularDecomposition R 𝔤}

variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

def homDim
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R) : ℤ :=
  ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu)

def grothendieck_group_has_inner_product
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ) :
    KO.InnerProductData :=
  { pairing := KO.pairing
    orthonormal := KO.pairing_orthonormal
    pairing_basis_determines := KO.pairing_basis_determines }

def IsInXi0
    (rd : PositiveRootData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ), lam - mu = ∑ α ∈ rd.posRoots, (c α) • α

def IsProperRep
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  IsDominantWeightBruhat rd wg lam ∧
  IsInXi0 rd mu lam ∧
  ∀ (w : wg.W), w ∈ WeylStabilizer rd wg lam →
    BruhatLE rd mu (wg.dualAction w mu)

def matrixCoeff
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (mu lam : Δ.𝔥 →ₗ[R] R) : ℤ :=
  ip.pairing (KO.delta mu) (fF.mapKO (KO.delta lam))

def supportPF
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO) : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | matrixCoeff KO ip fF p.1 p.2 > 0}

def maximalSupportPF
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg) [LE R] : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | p ∈ supportPF KO ip fF ∧
    ∀ q ∈ supportPF KO ip fF, B.normSq (q.2 - q.1) ≤ B.normSq (p.2 - p.1)}

def WeylOrbitPair
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | ∃ w : wg.W, p = (wg.dualAction w mu, wg.dualAction w lam)}

def SameInfChar
    (wg : WeylGroupData Δ)
    (nu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (w : wg.W), nu = wg.dualAction w lam

def IsZeroRepGfObj (M : RepGfObj R 𝔤) : Prop :=
  Subsingleton M.carrier

end Theorems
end

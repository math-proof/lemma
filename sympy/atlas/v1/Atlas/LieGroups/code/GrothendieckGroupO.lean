/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GrothendieckGroupO.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.ProjectiveFunctors
import Lemma.Int.IsDirectSummand
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections
import sympy.atlas.v1.Atlas.LieGroups.code.HeckeKL

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open ProjectiveFunctors Classical

universe u

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

structure GrothendieckGroupData (Δ : TriangularDecomposition R 𝔤) where
  carrier : Type u
  instACG : AddCommGroup carrier
  instMod : @Module ℤ carrier _ instACG.toAddCommMonoid
  delta : (Δ.𝔥 →ₗ[R] R) → carrier
  pairing : carrier → carrier → ℤ
  pairing_orthonormal : ∀ (lam mu : Δ.𝔥 →ₗ[R] R),
    pairing (delta lam) (delta mu) = if lam = mu then 1 else 0
  pairing_basis_determines :
    ∀ (h₁ h₂ : carrier → carrier → ℤ),
      (∀ lam mu : Δ.𝔥 →ₗ[R] R,
        h₁ (delta lam) (delta mu) = h₂ (delta lam) (delta mu)) →
      ∀ (x y : carrier), h₁ x y = h₂ x y

structure GrothendieckGroupData.InnerProductData
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ) where
  pairing : KO.carrier → KO.carrier → ℤ
  orthonormal : ∀ (lam mu : Δ.𝔥 →ₗ[R] R),
    pairing (KO.delta lam) (KO.delta mu) = if lam = mu then 1 else 0
  pairing_basis_determines :
    ∀ (h₁ h₂ : KO.carrier → KO.carrier → ℤ),
      (∀ lam mu : Δ.𝔥 →ₗ[R] R,
        h₁ (KO.delta lam) (KO.delta mu) = h₂ (KO.delta lam) (KO.delta mu)) →
      ∀ (x y : KO.carrier), h₁ x y = h₂ x y

structure InducedMapData
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ) where
  F : EndoFunctorData R 𝔤
  hF : IsProjectiveFunctor F
  mapKO : KO.carrier → KO.carrier
  map_basis_compat :
    ∀ (g : KO.carrier → KO.carrier),
      (∀ lam : Δ.𝔥 →ₗ[R] R, g (KO.delta lam) = mapKO (KO.delta lam)) →
      g = mapKO

structure WeylActionData
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ) where
  act : wg.W → KO.carrier → KO.carrier
  act_delta : ∀ (w : wg.W) (lam : Δ.𝔥 →ₗ[R] R),
    act w (KO.delta lam) = KO.delta (wg.dualAction w lam)

structure AdjointPairData where
  F : EndoFunctorData R 𝔤
  Fv : EndoFunctorData R 𝔤
  hF : IsProjectiveFunctor F
  hFv : IsProjectiveFunctor Fv
  adjunction_fwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom (F.obj M) N → RepGfHom M (Fv.obj N)
  adjunction_bwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom M (Fv.obj N) → RepGfHom (F.obj M) N
  adjunction_homDim_pairing :
    ∀ {Δ : TriangularDecomposition R 𝔤}
      (KO : GrothendieckGroupData Δ)
      (ip : KO.InnerProductData)
      (fF fFv : InducedMapData KO)
      (_ : fF.F = F) (_ : fFv.F = Fv)
      (lam mu : Δ.𝔥 →ₗ[R] R),
    ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) =
    ip.pairing (fFv.mapKO (KO.delta mu)) (KO.delta lam)

structure AdjointPairDataWeak where
  F : EndoFunctorData R 𝔤
  Fv : EndoFunctorData R 𝔤
  adjunction_fwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom (F.obj M) N → RepGfHom M (Fv.obj N)
  adjunction_bwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom M (Fv.obj N) → RepGfHom (F.obj M) N

def AdjointPairDataWeak.toAdjointPairData
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (hF : IsProjectiveFunctor adj.F)
    (hFv : IsProjectiveFunctor adj.Fv)
    (hDim : ∀ {Δ : TriangularDecomposition R 𝔤}
      (KO : GrothendieckGroupData Δ)
      (ip : KO.InnerProductData)
      (fF fFv : InducedMapData KO)
      (_ : fF.F = adj.F) (_ : fFv.F = adj.Fv)
      (lam mu : Δ.𝔥 →ₗ[R] R),
      ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) =
      ip.pairing (fFv.mapKO (KO.delta mu)) (KO.delta lam)) :
    AdjointPairData (R := R) (𝔤 := 𝔤) :=
  { F := adj.F
    Fv := adj.Fv
    hF := hF
    hFv := hFv
    adjunction_fwd := adj.adjunction_fwd
    adjunction_bwd := adj.adjunction_bwd
    adjunction_homDim_pairing := hDim }

def AdjointPairData.toWeak
    (adj : AdjointPairData (R := R) (𝔤 := 𝔤)) :
    AdjointPairDataWeak (R := R) (𝔤 := 𝔤) :=
  { F := adj.F
    Fv := adj.Fv
    adjunction_fwd := adj.adjunction_fwd
    adjunction_bwd := adj.adjunction_bwd }

@[simp] theorem AdjointPairData.toWeak_F (adj : AdjointPairData (R := R) (𝔤 := 𝔤)) :
    adj.toWeak.F = adj.F := rfl

@[simp] theorem AdjointPairData.toWeak_Fv (adj : AdjointPairData (R := R) (𝔤 := 𝔤)) :
    adj.toWeak.Fv = adj.Fv := rfl

def DominatesSet
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Prop :=
  ∀ mu ∈ S, rd.IsInQPlus (lam - mu)

structure WeightBilinForm {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ) where
  form : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R
  symm : ∀ (mu nu : Δ.𝔥 →ₗ[R] R), form mu nu = form nu mu
  bilin_left : ∀ (mu₁ mu₂ nu : Δ.𝔥 →ₗ[R] R),
    form (mu₁ + mu₂) nu = form mu₁ nu + form mu₂ nu
  weyl_normSq_invariant : ∀ (w : wg.W) (mu nu : Δ.𝔥 →ₗ[R] R),
    form (wg.dualAction w mu - wg.dualAction w nu)
         (wg.dualAction w mu - wg.dualAction w nu) = form (mu - nu) (mu - nu)
  pos_semidef : ∀ [LinearOrder R] [IsStrictOrderedRing R] (mu : Δ.𝔥 →ₗ[R] R),
    (0 : R) ≤ form mu mu
  form_corootPairing_compat :
    ∀ (rd : PositiveRootData Δ) (alpha mu : Δ.𝔥 →ₗ[R] R)
      (_ : alpha ∈ rd.posRoots),
    2 • form alpha mu = rd.corootPairing mu alpha * form alpha alpha
  dominant_corootPairing_diff_nonneg :
    ∀ [LinearOrder R] [IsStrictOrderedRing R]
      (rd : PositiveRootData Δ)
      (lam phi alpha : Δ.𝔥 →ₗ[R] R)
      (_ : IsDominantWeightBruhat rd wg lam)
      (_ : BruhatLE rd phi lam)
      (_ : alpha ∈ rd.posRoots),
    (0 : R) ≤ rd.corootPairing (lam - phi) alpha
  form_coroot_compat :
    ∀ (rd : PositiveRootData Δ) (rs : RootSystemWithReflections rd wg)
      (alpha mu : Δ.𝔥 →ₗ[R] R)
      (_ : alpha ∈ rs.allRoots),
    2 • form alpha mu = mu (rs.coroot alpha) * form alpha alpha
  form_posRoot_pos :
    ∀ [LinearOrder R] [IsStrictOrderedRing R]
      (rd : PositiveRootData Δ)
      (alpha : Δ.𝔥 →ₗ[R] R)
      (_ : alpha ∈ rd.posRoots),
    (0 : R) < form alpha alpha

def WeightBilinForm.normSq {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg) (mu : Δ.𝔥 →ₗ[R] R) : R :=
  B.form mu mu

structure GrothendieckGroupBlock
    (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) where
  carrier : Type u
  instACG : AddCommGroup carrier
  instMod : @Module ℤ carrier _ instACG.toAddCommMonoid
  delta_w : wg.W → carrier
  basis_injective : Function.Injective delta_w
  basis_linearIndep :
    letI := instACG; letI := instMod
    ∀ (c : wg.W → ℤ),
      (Finset.univ.sum (fun w => (c w) • (delta_w w)) = (0 : carrier)) →
      ∀ w, c w = 0

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

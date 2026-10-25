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

end

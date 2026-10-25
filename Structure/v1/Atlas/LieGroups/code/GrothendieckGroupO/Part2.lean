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
import Def.v1.Atlas.LieGroups.code.GrothendieckGroupO.Part2
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false


noncomputable section

open scoped TensorProduct

open ProjectiveFunctors Classical

universe u

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

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

end

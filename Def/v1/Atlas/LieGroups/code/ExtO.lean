/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ExtO.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.BGGReciprocity.Part3
import Lemma.Int.All_Eq_0.of.EqCompositionLengthO_0.IsCategoryO
import Lemma.Finset.EqMul_Mul.of.In_SimpleReflections
import Def.v1.Atlas.LieGroups.code.HeckeKL.Part9


noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def ExtOVanishes
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ} :
    ℕ →
    (X : Type uCatO) → [AddCommGroup X] → [Module R X] →
    [LieRingModule 𝔤 X] → [LieModule R 𝔤 X] →
    (IsCategoryO Δ rd X) →
    (Y : Type uCatO) → [AddCommGroup Y] → [Module R Y] →
    [LieRingModule 𝔤 Y] → [LieModule R 𝔤 Y] →
    (IsCategoryO Δ rd Y) →
    Prop
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => True
  | 1, X, _, _, _, _, _, Y, _, _, _, _, _ =>
    ∀ (E : Type uCatO) [AddCommGroup E] [Module R E]
      [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
      (_ : IsCategoryO Δ rd E)
      (ι : Y →ₗ⁅R, 𝔤⁆ E) (_ : Function.Injective ι)
      (p : E →ₗ⁅R, 𝔤⁆ X) (_ : Function.Surjective p)
      (_ : ∀ e : E, p e = 0 ↔ ∃ m : Y, ι m = e),
      ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x
  | (n + 2), X, _, _, _, _, _, Y, _, _, _, _, hYO =>
    ∀ (K : Type uCatO) [AddCommGroup K] [Module R K]
      [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
      (hKO : IsCategoryO Δ rd K)
      (P : Type uCatO) [AddCommGroup P] [Module R P]
      [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
      (hPO : IsCategoryO Δ rd P)
      (_ : IsProjectiveInO rd P hPO)
      (ι : K →ₗ⁅R, 𝔤⁆ P) (_ : Function.Injective ι)
      (p : P →ₗ⁅R, 𝔤⁆ X) (_ : Function.Surjective p)
      (_ : ∀ q, p q = 0 ↔ ∃ k, ι k = q),
      ExtOVanishes (n + 1) K hKO Y hYO


end

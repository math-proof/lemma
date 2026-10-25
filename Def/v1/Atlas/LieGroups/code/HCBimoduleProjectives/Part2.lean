/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HCBimoduleProjectives.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.LieGroups.code.MaximalQuotients
import Lemma.Int.Any_EqUeaAction
import Mathlib.Algebra.Lie.Semisimple.Defs
import Structure.v1.Atlas.LieGroups.code.HCBimoduleProjectives.Part2


noncomputable section

universe u_R u_𝔤 u_mod

variable {R : Type u_R} [CommRing R]

variable {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]

def IsInHC (M : LieBimodule R 𝔤) : Prop :=
  IsHarishChandraBimodule M

def LieBimodule.AreIsomorphic (M₁ M₂ : LieBimodule R 𝔤) : Prop :=
  ∃ (f : M₁.carrier →ₗ[R] M₂.carrier),
    Function.Bijective f ∧
    (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M₁.carrier),
      f (M₁.leftAction u m) = M₂.leftAction u (f m)) ∧
    (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : M₁.carrier),
      f (M₁.rightAction u m) = M₂.rightAction u (f m))

section Corollary_25_7

universe u_𝔤'' u_mod''

variable {𝔤'' : Type u_𝔤''} [LieRing 𝔤''] [LieAlgebra ℂ 𝔤'']
  [LieAlgebra.IsSemisimple ℂ 𝔤''] [Module.Finite ℂ 𝔤'']

def HasFinitelyManySimpleBimodules
    {𝔤 : Type u_𝔤''} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (θ : CenterCharacter ℂ 𝔤) : Prop :=
  ∃ (n : ℕ) (simples : Fin n → LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤),
    (∀ i, (simples i).IsIrreducible) ∧
    (∀ i, IsInHCThetaOne (simples i) θ) ∧
    (∀ (S : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤), S.IsIrreducible → IsInHCThetaOne S θ →
      ∃ i, LieBimodule.AreIsomorphic S (simples i))

end Corollary_25_7
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TranslationFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.FGUeaIotaRange
import Lemma.Int.All_Eq_0.of.EqCompositionLengthO_0.IsCategoryO
import Lemma.Int.IsCategoryOA.of.IsCategoryOB
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
import Def.v1.Atlas.LieGroups.code.BGGReciprocity.Part3
import Structure.v1.Atlas.LieGroups.code.TensorO
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Semisimple.Basic
import Theorem.v1.Atlas.LieGroups.code.TranslationFunctors


noncomputable section

open scoped TensorProduct

universe uM

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable (Δ : TriangularDecomposition R 𝔤)

variable (rd : PositiveRootData Δ)

variable (wg : WeylGroupData Δ)

local notation "𝔥*" => (Δ.𝔥 →ₗ[R] R)

attribute [instance] TranslationFunctorData.V_addCommGroup
  TranslationFunctorData.V_module TranslationFunctorData.V_lieRingModule
  TranslationFunctorData.V_lieModule TranslationFunctorData.V_finiteDim
  TranslationFunctorData.V_irreducible

attribute [instance] TranslationFunctorData.ApplyResult.instAddCommGroup
  TranslationFunctorData.ApplyResult.instModule
  TranslationFunctorData.ApplyResult.instLieRingModule
  TranslationFunctorData.ApplyResult.instLieModule

section CharEigenspace

variable {R : Type*} [CommRing R]

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {M : Type*} [AddCommGroup M] [Module R M]

variable [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

variable (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)

variable (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)

def charEigenspaceLie
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    LieSubmodule R 𝔤 M where
  __ := charEigenspace act χ
  lie_mem {x m} hm := by
    show ⁅x, m⁆ ∈ charEigenspace act χ
    rw [← hcompat x m]
    exact charEigenspace_closed_uea act χ (UniversalEnvelopingAlgebra.ι R x) hm

noncomputable def restrictedUEAAction
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R]
      Module.End R ↥(charEigenspaceLie act χ hcompat) where
  toFun u :=
    { toFun := fun ⟨m, hm⟩ =>
        ⟨act u m, charEigenspace_closed_uea act χ u hm⟩
      map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => by simp [Subtype.ext_iff, map_add]
      map_smul' := fun r ⟨m, _⟩ => by simp [Subtype.ext_iff, (act u).map_smul] }
  map_one' := by ext ⟨m, _⟩; simp [map_one]
  map_mul' a b := by
    ext ⟨m, _⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    show (act (a * b) m : M) = act a (act b m)
    rw [map_mul]; rfl
  map_zero' := by ext ⟨m, _⟩; simp [map_zero]
  map_add' a b := by
    ext ⟨m, _⟩; simp [map_add, LinearMap.add_apply]
  commutes' r := by
    ext ⟨m, _⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    show (act (algebraMap R _ r) m : M) = r • m
    rw [AlgHom.commutes]; rfl

end CharEigenspace
end

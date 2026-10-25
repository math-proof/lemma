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
import Structure.v1.Atlas.LieGroups.code.TranslationFunctors


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

def charEigenspace : Submodule R M where
  carrier := {m : M | ∀ z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
    act (z : UniversalEnvelopingAlgebra R 𝔤) m = χ z • m}
  zero_mem' z := by simp [map_zero, smul_zero]
  add_mem' {a b} ha hb z := by simp [map_add, ha z, hb z, smul_add]
  smul_mem' r m hm z := by
    show act (↑z) (r • m) = χ z • (r • m)
    rw [(act (↑z)).map_smul, hm z, smul_comm]

end CharEigenspace
end

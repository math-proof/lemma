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
import Def.v1.Atlas.LieGroups.code.TranslationFunctors


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

set_option linter.unusedSectionVars false in
theorem charEigenspace_closed_uea (u : UniversalEnvelopingAlgebra R 𝔤) {m : M}
    (hm : m ∈ charEigenspace act χ) :
    act u m ∈ charEigenspace act χ := by
  intro z

  have h1 : (act (↑z)) ((act u) m) =
      (act ((↑z : UniversalEnvelopingAlgebra R 𝔤) * u)) m := by
    rw [map_mul]; rfl

  have hc : (z : UniversalEnvelopingAlgebra R 𝔤) * u =
      u * (z : UniversalEnvelopingAlgebra R 𝔤) :=
    ((Subalgebra.mem_center_iff.mp z.property) u).symm

  have h2 : (act (u * (↑z : UniversalEnvelopingAlgebra R 𝔤))) m =
      (act u) ((act (↑z)) m) := by
    rw [map_mul]; rfl
  rw [h1, hc, h2, hm z, (act u).map_smul]

end CharEigenspace
end

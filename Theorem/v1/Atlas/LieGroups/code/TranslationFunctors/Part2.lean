module
public import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
public import Theorem.Int.WeightLE.of.BruhatLE
public import Theorem.Int.FGUeaIotaRange
public import Theorem.Int.All_Eq_0.of.EqCompositionLengthO_0.IsCategoryO
public import Theorem.Int.IsCategoryOA.of.IsCategoryOB
public import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
public import Def.v1.Atlas.LieGroups.code.BGGReciprocity.Part3
public import Structure.v1.Atlas.LieGroups.code.TensorO
public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Def.v1.Atlas.LieGroups.code.TranslationFunctors.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/TranslationFunctors.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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

theorem restrictedUEAAction_compat
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (x : 𝔤) (m : ↥(charEigenspaceLie act χ hcompat)) :
    restrictedUEAAction act χ hcompat (UniversalEnvelopingAlgebra.ι R x) m =
      ⁅x, m⁆ := by
  ext; simp [restrictedUEAAction]; exact hcompat x ↑m

theorem restrictedUEA_center_acts
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))
    (m : ↥(charEigenspaceLie act χ hcompat)) :
    restrictedUEAAction act χ hcompat
      (z : UniversalEnvelopingAlgebra R 𝔤) m = χ z • m := by
  ext; simp [restrictedUEAAction]; exact m.property z

end CharEigenspace
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BeilinsonBernstein.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Def.v1.Atlas.LieGroups.code.BeilinsonBernstein.Part3
open CategoryTheory


namespace BeilinsonBernstein

noncomputable section

universe u

attribute [instance] CAlgebra.instRing CAlgebra.instAlgebra

attribute [instance] AbCat.instCat

attribute [instance] GradedAlgebra.instRing GradedAlgebra.instAlgebra

attribute [instance] BBDataZero.instLieRing BBDataZero.instLieAlgebra BBDataZero.instSemisimple

structure PartialFlagData where
  gLie : Type u
  instLieRing : LieRing gLie
  instLieAlgebra : LieAlgebra ℂ gLie
  instSemisimple : LieAlgebra.IsSemisimple ℂ gLie
  X : SmoothAlgVariety.{u}
  DX : CAlgebra.{u}
  DMod : AbCat.{u}
  DXMod : AbCat.{u}
  Gamma : DMod.Obj ⥤ DXMod.Obj
  Loc : DXMod.Obj ⥤ DMod.Obj

attribute [instance] PartialFlagData.instLieRing PartialFlagData.instLieAlgebra
  PartialFlagData.instSemisimple

structure TwistedDiffOps (X : SmoothAlgVariety.{u}) (WeightSpace : Type u) where
  weight : WeightSpace
  algebra : CAlgebra.{u}

structure TwistedDModuleCat (X : SmoothAlgVariety.{u}) (WeightSpace : Type u) where
  weight : WeightSpace
  cat : AbCat.{u}

structure BBDataTwisted where
  gLie : Type u
  instLieRing : LieRing gLie
  instLieAlgebra : LieAlgebra ℂ gLie
  instSemisimple : LieAlgebra.IsSemisimple ℂ gLie
  WeightSpace : Type u
  IsAntidominant : WeightSpace → Prop
  FlagVar : SmoothAlgVariety.{u}
  DOfWeight : WeightSpace → CAlgebra.{u}
  UOfWeight : WeightSpace → CAlgebra.{u}
  projOfWeight : (mu : WeightSpace) →
    @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra →ₐ[ℂ]
      (UOfWeight mu).carrier
  actionMapOfWeight : (mu : WeightSpace) →
    @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra →ₐ[ℂ]
      (DOfWeight mu).carrier
  aOfWeight : (mu : WeightSpace) →
    (UOfWeight mu).carrier →ₐ[ℂ] (DOfWeight mu).carrier


  NilpCone : Type u
  CotangentBundle : Type u
  grUOfWeight : WeightSpace → GradedAlgebra.{u}
  grDOfWeight : WeightSpace → GradedAlgebra.{u}
  O_TstarF : GradedAlgebra.{u}
  gr_aOfWeight : (mu : WeightSpace) →
    (grUOfWeight mu).carrier →ₐ[ℂ] (grDOfWeight mu).carrier
  p_starOfWeight : (mu : WeightSpace) →
    (grUOfWeight mu).carrier →ₐ[ℂ] O_TstarF.carrier
  incl_TstarFOfWeight : (mu : WeightSpace) →
    O_TstarF.carrier →ₐ[ℂ] (grDOfWeight mu).carrier
  p_starOfWeight_bijective : ∀ mu : WeightSpace,
    Function.Bijective (p_starOfWeight mu)
  symbol_projOfWeight : (mu : WeightSpace) →
    (grDOfWeight mu).carrier →ₐ[ℂ] O_TstarF.carrier
  symbol_projOfWeight_left_inv : ∀ (mu : WeightSpace),
    Function.LeftInverse (symbol_projOfWeight mu) (incl_TstarFOfWeight mu)

  generators_grUOfWeight : (mu : WeightSpace) → Set (grUOfWeight mu).carrier
  grUOfWeight_generated : ∀ mu : WeightSpace,
    Algebra.adjoin ℂ (generators_grUOfWeight mu) = ⊤
  generators_grUOfWeight_deg1 : (mu : WeightSpace) → Set (grUOfWeight mu).carrier
  generators_grUOfWeight_decomp : ∀ mu : WeightSpace,
    generators_grUOfWeight mu ⊆
      Set.range (algebraMap ℂ (grUOfWeight mu).carrier) ∪ generators_grUOfWeight_deg1 mu
  symbolOfActionOfWeight : (mu : WeightSpace) →
    (grUOfWeight mu).carrier → (grDOfWeight mu).carrier
  gr_aOfWeight_eq_symbolOfAction_field : ∀ (mu : WeightSpace)
    (x : (grUOfWeight mu).carrier), x ∈ generators_grUOfWeight_deg1 mu →
    gr_aOfWeight mu x = symbolOfActionOfWeight mu x
  incl_p_star_eq_symbolOfActionOfWeight_field : ∀ (mu : WeightSpace)
    (x : (grUOfWeight mu).carrier), x ∈ generators_grUOfWeight_deg1 mu →
    (incl_TstarFOfWeight mu).comp (p_starOfWeight mu) x =
      symbolOfActionOfWeight mu x


  filtration_UOfWeight : (mu : WeightSpace) → ℕ → Submodule ℂ (UOfWeight mu).carrier
  filtration_DOfWeight : (mu : WeightSpace) → ℕ → Submodule ℂ (DOfWeight mu).carrier
  filtration_UOfWeight_exhaustive : ∀ mu x, ∃ n, x ∈ filtration_UOfWeight mu n
  filtration_UOfWeight_mono : ∀ mu, ∀ ⦃m n⦄, m ≤ n →
    filtration_UOfWeight mu m ≤ filtration_UOfWeight mu n

  filtration_DOfWeight_exhaustive : ∀ mu y, ∃ n, y ∈ filtration_DOfWeight mu n


  DModOfWeight : WeightSpace → AbCat.{u}
  UModOfWeight : WeightSpace → AbCat.{u}
  GammaOfWeight : (mu : WeightSpace) → (DModOfWeight mu).Obj ⥤ (UModOfWeight mu).Obj
  LocOfWeight : (mu : WeightSpace) → (UModOfWeight mu).Obj ⥤ (DModOfWeight mu).Obj

  aOfWeight_filtration_preserving : ∀ mu n (x : (UOfWeight mu).carrier),
    x ∈ filtration_UOfWeight mu n → aOfWeight mu x ∈ filtration_DOfWeight mu n
  quotient_UOfWeight : (mu : WeightSpace) → (n : ℕ) →
    { x : (UOfWeight mu).carrier // x ∈ filtration_UOfWeight mu n } → (grUOfWeight mu).carrier
  quotient_DOfWeight : (mu : WeightSpace) → (n : ℕ) →
    { y : (DOfWeight mu).carrier // y ∈ filtration_DOfWeight mu n } → (grDOfWeight mu).carrier
  quotient_UOfWeight_ker : ∀ mu n (x : (UOfWeight mu).carrier)
    (hx : x ∈ filtration_UOfWeight mu n),
    quotient_UOfWeight mu n ⟨x, hx⟩ = 0 ↔ x ∈ filtPred (filtration_UOfWeight mu) n
  quotient_DOfWeight_ker : ∀ mu n (y : (DOfWeight mu).carrier)
    (hy : y ∈ filtration_DOfWeight mu n),
    quotient_DOfWeight mu n ⟨y, hy⟩ = 0 ↔ y ∈ filtPred (filtration_DOfWeight mu) n
  gr_aOfWeight_compat : ∀ mu n (x : (UOfWeight mu).carrier)
    (hx : x ∈ filtration_UOfWeight mu n),
    gr_aOfWeight mu (quotient_UOfWeight mu n ⟨x, hx⟩) =
      quotient_DOfWeight mu n ⟨aOfWeight mu x, aOfWeight_filtration_preserving mu n x hx⟩
  quotient_DOfWeight_sub : ∀ mu n (y₁ y₂ : (DOfWeight mu).carrier)
    (hy₁ : y₁ ∈ filtration_DOfWeight mu n) (hy₂ : y₂ ∈ filtration_DOfWeight mu n)
    (hy_sub : y₁ - y₂ ∈ filtration_DOfWeight mu n),
    quotient_DOfWeight mu n ⟨y₁ - y₂, hy_sub⟩ =
      quotient_DOfWeight mu n ⟨y₁, hy₁⟩ - quotient_DOfWeight mu n ⟨y₂, hy₂⟩
  filtration_DOfWeight_mono : ∀ mu, ∀ ⦃m n⦄, m ≤ n →
    filtration_DOfWeight mu m ≤ filtration_DOfWeight mu n
  quotient_DOfWeight_surj : ∀ mu (z : (grDOfWeight mu).carrier),
    ∃ n, ∃ y : (DOfWeight mu).carrier, ∃ hy : y ∈ filtration_DOfWeight mu n,
      quotient_DOfWeight mu n ⟨y, hy⟩ = z
  quotient_UOfWeight_surj : ∀ mu (z : (grUOfWeight mu).carrier),
    ∃ n, ∃ x : (UOfWeight mu).carrier, ∃ hx : x ∈ filtration_UOfWeight mu n,
      quotient_UOfWeight mu n ⟨x, hx⟩ = z
  aOfWeight_factors_field : ∀ (mu : WeightSpace)
    (x : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra),
    aOfWeight mu (projOfWeight mu x) = actionMapOfWeight mu x
  actionMapOfWeight_surjective_field : ∀ (mu : WeightSpace),
    Function.Surjective (actionMapOfWeight mu)
  gr_aOfWeight_approx_surj : ∀ (mu : WeightSpace) (n : ℕ)
    (y : (DOfWeight mu).carrier) (hy : y ∈ filtration_DOfWeight mu n),
    ∃ (x : (UOfWeight mu).carrier) (hx : x ∈ filtration_UOfWeight mu n),
      quotient_DOfWeight mu n ⟨aOfWeight mu x, aOfWeight_filtration_preserving mu n x hx⟩ =
        quotient_DOfWeight mu n ⟨y, hy⟩

end
end BeilinsonBernstein

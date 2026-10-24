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

open CategoryTheory

namespace BeilinsonBernstein

noncomputable section

universe u

structure SmoothAlgVariety where
  carrier : Type u

structure CAlgebra where
  carrier : Type u
  instRing : Ring carrier
  instAlgebra : Algebra ℂ carrier

attribute [instance] CAlgebra.instRing CAlgebra.instAlgebra

structure AbCat where
  Obj : Type u
  instCat : Category Obj

attribute [instance] AbCat.instCat

structure GradedAlgebra where
  carrier : Type u
  instRing : Ring carrier
  instAlgebra : Algebra ℂ carrier

attribute [instance] GradedAlgebra.instRing GradedAlgebra.instAlgebra

def filtPred {α : Type*} [AddCommMonoid α] [Module ℂ α]
    (F : ℕ → Submodule ℂ α) : ℕ → Submodule ℂ α
  | 0 => ⊥
  | n + 1 => F n

class IsDaffine (X : SmoothAlgVariety.{u}) (DMod : AbCat.{u}) (DXMod : AbCat.{u})
    (Gamma : DMod.Obj ⥤ DXMod.Obj) (Loc : DXMod.Obj ⥤ DMod.Obj) : Prop where
  equiv : ∃ e : DMod.Obj ≌ DXMod.Obj, e.functor = Gamma ∧ e.inverse = Loc

noncomputable def AlgHom.liftOfSurjectiveNC {R A B C : Type*}
    [CommSemiring R] [Ring A] [Ring B] [Ring C]
    [Algebra R A] [Algebra R B] [Algebra R C]
    (π : A →ₐ[R] B) (hπ : Function.Surjective π) (f : A →ₐ[R] C)
    (hker : ∀ x, π x = 0 → f x = 0) : B →ₐ[R] C where
  toFun b := f (Function.surjInv hπ b)
  map_one' := by
    have hk : π (Function.surjInv hπ 1 - 1) = 0 := by simp [Function.surjInv_eq]
    have := hker _ hk; rwa [map_sub, map_one, sub_eq_zero] at this
  map_mul' x y := by
    obtain ⟨a, rfl⟩ := hπ x; obtain ⟨b, rfl⟩ := hπ y
    have hab := hker _ (show π (Function.surjInv hπ (π a * π b) - a * b) = 0 by
      rw [← map_mul]; simp [Function.surjInv_eq])
    rw [map_sub, map_mul, sub_eq_zero] at hab
    have ha := hker _ (show π (Function.surjInv hπ (π a) - a) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at ha
    have hb := hker _ (show π (Function.surjInv hπ (π b) - b) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at hb; rw [hab, ha, hb]
  map_zero' := hker _ (by simp [Function.surjInv_eq])
  map_add' x y := by
    obtain ⟨a, rfl⟩ := hπ x; obtain ⟨b, rfl⟩ := hπ y
    have hab := hker _ (show π (Function.surjInv hπ (π a + π b) - (a + b)) = 0 by
      rw [← map_add]; simp [Function.surjInv_eq])
    rw [map_sub, map_add, sub_eq_zero] at hab
    have ha := hker _ (show π (Function.surjInv hπ (π a) - a) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at ha
    have hb := hker _ (show π (Function.surjInv hπ (π b) - b) = 0 by
      simp [Function.surjInv_eq])
    rw [map_sub, sub_eq_zero] at hb; rw [hab, ha, hb]
  commutes' r := by
    have := hker _ (show π (Function.surjInv hπ (algebraMap R B r) - algebraMap R A r) = 0 by
      simp [Function.surjInv_eq, AlgHom.commutes])
    rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this

structure BBDataZero where
  gLie : Type u
  instLieRing : LieRing gLie
  instLieAlgebra : LieAlgebra ℂ gLie
  instSemisimple : LieAlgebra.IsSemisimple ℂ gLie
  FlagVar : SmoothAlgVariety.{u}
  DF : CAlgebra.{u}
  U₀ : CAlgebra.{u}
  proj₀ : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra →ₐ[ℂ] U₀.carrier
  actionMap : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra →ₐ[ℂ] DF.carrier
  proj₀_surjective : Function.Surjective proj₀
  ker_inclusion : ∀ (x : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra),
    proj₀ x = 0 → actionMap x = 0


  NilpCone : Type u
  CotangentBundle : Type u
  grU₀ : GradedAlgebra.{u}
  grDF : GradedAlgebra.{u}
  O_TstarF : GradedAlgebra.{u}
  gr_a₀ : grU₀.carrier →ₐ[ℂ] grDF.carrier
  p_star : grU₀.carrier →ₐ[ℂ] O_TstarF.carrier
  incl_TstarF : O_TstarF.carrier →ₐ[ℂ] grDF.carrier
  p_star_bijective : Function.Bijective p_star
  symbol_proj : grDF.carrier →ₐ[ℂ] O_TstarF.carrier
  symbol_proj_left_inv : Function.LeftInverse symbol_proj incl_TstarF
  generators_grU₀ : Set grU₀.carrier
  grU₀_generated : Algebra.adjoin ℂ generators_grU₀ = ⊤
  generators_grU₀_deg1 : Set grU₀.carrier
  generators_grU₀_decomp : generators_grU₀ ⊆
    Set.range (algebraMap ℂ grU₀.carrier) ∪ generators_grU₀_deg1
  symbolOfAction : grU₀.carrier → grDF.carrier
  gr_a₀_eq_symbolOfAction_field : ∀ x ∈ generators_grU₀_deg1, gr_a₀ x = symbolOfAction x
  incl_p_star_eq_symbolOfAction_field : ∀ x ∈ generators_grU₀_deg1,
    (incl_TstarF.comp p_star) x = symbolOfAction x

  DModF : AbCat.{u}
  U₀Mod : AbCat.{u}
  Gamma : DModF.Obj ⥤ U₀Mod.Obj
  Loc : U₀Mod.Obj ⥤ DModF.Obj

  filtration_U₀ : ℕ → Submodule ℂ U₀.carrier
  filtration_DF : ℕ → Submodule ℂ DF.carrier
  filtration_U₀_exhaustive : ∀ x, ∃ n, x ∈ filtration_U₀ n
  filtration_U₀_mono : ∀ ⦃m n⦄, m ≤ n → filtration_U₀ m ≤ filtration_U₀ n

  filtration_DF_exhaustive : ∀ y, ∃ n, y ∈ filtration_DF n

  quotient_U₀ : (n : ℕ) → { x : U₀.carrier // x ∈ filtration_U₀ n } → grU₀.carrier
  quotient_DF : (n : ℕ) → { y : DF.carrier // y ∈ filtration_DF n } → grDF.carrier
  quotient_U₀_ker : ∀ n (x : U₀.carrier) (hx : x ∈ filtration_U₀ n),
    quotient_U₀ n ⟨x, hx⟩ = 0 ↔ x ∈ filtPred filtration_U₀ n
  quotient_DF_ker : ∀ n (y : DF.carrier) (hy : y ∈ filtration_DF n),
    quotient_DF n ⟨y, hy⟩ = 0 ↔ y ∈ filtPred filtration_DF n

  quotient_DF_sub : ∀ n (y₁ y₂ : DF.carrier) (hy₁ : y₁ ∈ filtration_DF n)
    (hy₂ : y₂ ∈ filtration_DF n) (hy_sub : y₁ - y₂ ∈ filtration_DF n),
    quotient_DF n ⟨y₁ - y₂, hy_sub⟩ = quotient_DF n ⟨y₁, hy₁⟩ - quotient_DF n ⟨y₂, hy₂⟩
  filtration_DF_mono : ∀ ⦃m n⦄, m ≤ n → filtration_DF m ≤ filtration_DF n
  quotient_U₀_add : ∀ n (x₁ x₂ : U₀.carrier) (hx₁ : x₁ ∈ filtration_U₀ n)
    (hx₂ : x₂ ∈ filtration_U₀ n) (hx_add : x₁ + x₂ ∈ filtration_U₀ n),
    quotient_U₀ n ⟨x₁ + x₂, hx_add⟩ = quotient_U₀ n ⟨x₁, hx₁⟩ + quotient_U₀ n ⟨x₂, hx₂⟩
  quotient_U₀_sub : ∀ n (x₁ x₂ : U₀.carrier) (hx₁ : x₁ ∈ filtration_U₀ n)
    (hx₂ : x₂ ∈ filtration_U₀ n) (hx_sub : x₁ - x₂ ∈ filtration_U₀ n),
    quotient_U₀ n ⟨x₁ - x₂, hx_sub⟩ = quotient_U₀ n ⟨x₁, hx₁⟩ - quotient_U₀ n ⟨x₂, hx₂⟩
  quotient_DF_add : ∀ n (y₁ y₂ : DF.carrier) (hy₁ : y₁ ∈ filtration_DF n)
    (hy₂ : y₂ ∈ filtration_DF n) (hy_add : y₁ + y₂ ∈ filtration_DF n),
    quotient_DF n ⟨y₁ + y₂, hy_add⟩ = quotient_DF n ⟨y₁, hy₁⟩ + quotient_DF n ⟨y₂, hy₂⟩
  quotient_DF_surj : ∀ z : grDF.carrier,
    ∃ n, ∃ y : DF.carrier, ∃ hy : y ∈ filtration_DF n, quotient_DF n ⟨y, hy⟩ = z
  quotient_U₀_surj : ∀ z : grU₀.carrier,
    ∃ n, ∃ x : U₀.carrier, ∃ hx : x ∈ filtration_U₀ n, quotient_U₀ n ⟨x, hx⟩ = z
  filtration_UEA : ℕ → Submodule ℂ
    (@UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra)
  actionMap_filtration_preserving :
    ∀ n (u : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra),
    u ∈ filtration_UEA n → actionMap u ∈ filtration_DF n
  proj₀_filtration_surj : ∀ n (x : U₀.carrier),
    x ∈ filtration_U₀ n →
    ∃ u : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra,
      u ∈ filtration_UEA n ∧ proj₀ u = x
  gr_a₀_compat_UEA :
    ∀ n (u : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra)
      (hu : u ∈ filtration_UEA n)
      (hpu : proj₀ u ∈ filtration_U₀ n),
      gr_a₀ (quotient_U₀ n ⟨proj₀ u, hpu⟩) =
        quotient_DF n ⟨actionMap u, actionMap_filtration_preserving n u hu⟩

  symbol_proj_right_inv : Function.RightInverse symbol_proj incl_TstarF
  gr_a₀_approx_surj : ∀ (n : ℕ) (y : DF.carrier) (hy : y ∈ filtration_DF n),
    ∃ (u : @UniversalEnvelopingAlgebra ℂ gLie _ instLieRing instLieAlgebra)
      (hu : u ∈ filtration_UEA n) (_ : proj₀ u ∈ filtration_U₀ n),
      quotient_DF n ⟨actionMap u, actionMap_filtration_preserving n u hu⟩ =
        quotient_DF n ⟨y, hy⟩

attribute [instance] BBDataZero.instLieRing BBDataZero.instLieAlgebra BBDataZero.instSemisimple

noncomputable def BBDataZero.a₀ (D : BBDataZero) : D.U₀.carrier →ₐ[ℂ] D.DF.carrier :=
  AlgHom.liftOfSurjectiveNC D.proj₀ D.proj₀_surjective D.actionMap D.ker_inclusion

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

attribute [instance] BBDataTwisted.instLieRing BBDataTwisted.instLieAlgebra
  BBDataTwisted.instSemisimple

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
import Def.v1.Atlas.LieGroups.code.BeilinsonBernstein.Part2
open CategoryTheory


namespace BeilinsonBernstein

noncomputable section

universe u

attribute [instance] CAlgebra.instRing CAlgebra.instAlgebra

attribute [instance] AbCat.instCat

attribute [instance] GradedAlgebra.instRing GradedAlgebra.instAlgebra

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

end
end BeilinsonBernstein

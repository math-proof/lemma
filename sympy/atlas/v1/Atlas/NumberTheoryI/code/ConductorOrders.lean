/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ConductorOrders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Conductor
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.Algebra.Module.Lattice
import Mathlib.Tactic.LinearCombination

noncomputable section

open Ideal Polynomial Algebra IsDedekindDomain nonZeroDivisors

section ConductorDef

variable (R : Type*) (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

def Subalgebra.conductorIdeal (A : Subalgebra R S) : Ideal S where
  carrier := {a : S | ∀ b : S, a * b ∈ A}
  zero_mem' b := by simp [A.zero_mem]
  add_mem' {a₁ a₂} ha₁ ha₂ b := by rw [add_mul]; exact A.add_mem (ha₁ b) (ha₂ b)
  smul_mem' c a ha b := by
    simp only [smul_eq_mul, Set.mem_setOf_eq] at *
    rw [show c * a * b = a * (c * b) by ring]
    exact ha (c * b)

variable {R S}

end ConductorDef

section OrderDef

class IsOrder (O : Type*) [CommRing O] [IsDomain O] : Prop where
  isNoetherian : IsNoetherianRing O
  dimLEOne : Ring.DimensionLEOne O
  notIsField : ¬ IsField O
  intClosureFG : ∀ (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K],
    Module.Finite O (integralClosure O K)

class IsAOrder (A : Type*) (L : Type*) [CommRing A] [CommRing L] [Algebra A L]
    (O : Subalgebra A L) : Prop where
  fg : (O.toSubmodule).FG
  spans : ∀ (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L],
    Submodule.span K (Set.range (Subtype.val : O → L)) = ⊤

end OrderDef

section ConductorFiniteness

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

omit [IsDomain A] in
lemma nonZeroDivisors_le_comap_atPrime (𝔭 : Ideal A) [𝔭.IsPrime] :
    A⁰ ≤ Submonoid.comap (algebraMap A (Localization.AtPrime 𝔭)) (Localization.AtPrime 𝔭)⁰ := by
  intro a ha
  rw [Submonoid.mem_comap]
  exact IsLocalization.map_nonZeroDivisors_le 𝔭.primeCompl (Localization.AtPrime 𝔭) ⟨a, ha, rfl⟩


def FractionalIdeal.IsPrimeTo [IsNoetherianRing A]
    (I : FractionalIdeal A⁰ (Localization A⁰)) (J : Ideal A) : Prop :=
  ∀ (𝔭 : Ideal A) [𝔭.IsPrime], J ≤ 𝔭 →
    FractionalIdeal.extended (Localization A⁰) (nonZeroDivisors_le_comap_atPrime 𝔭) I = 1

variable [IsNoetherianRing A]

def invertibleFractionalIdealsPrimeTo (J : Ideal A) :
    Subgroup (FractionalIdeal A⁰ (Localization A⁰))ˣ where
  carrier := {u | (u : FractionalIdeal A⁰ (Localization A⁰)).IsPrimeTo J}
  one_mem' := by
    intro 𝔭 _ _
    exact FractionalIdeal.extended_one _ _
  mul_mem' := by
    intro a b ha hb 𝔭 _ h𝔭
    simp only [Units.val_mul]
    rw [FractionalIdeal.extended_mul, ha 𝔭 h𝔭, hb 𝔭 h𝔭, one_mul]
  inv_mem' := by
    intro a ha 𝔭 _ h𝔭
    have h1 : FractionalIdeal.extended (Localization A⁰) (nonZeroDivisors_le_comap_atPrime 𝔭)
        (↑(a * a⁻¹) : FractionalIdeal A⁰ (Localization A⁰)) = 1 := by
      simp [FractionalIdeal.extended_one]
    rw [Units.val_mul, FractionalIdeal.extended_mul, ha 𝔭 h𝔭, one_mul] at h1
    exact h1

end FractionalIdealPrimeTo

section FaithfulStatements

class IsAOrder_AKLB (A : Type*) (L : Type*)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing L] [IsDomain L] [Algebra A L]
    (O : Subalgebra A L) : Prop where
  fg : (O.toSubmodule).FG
  spans : ∀ (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [IsScalarTower A K L],
    Submodule.span K (Set.range (Subtype.val : O → L)) = ⊤

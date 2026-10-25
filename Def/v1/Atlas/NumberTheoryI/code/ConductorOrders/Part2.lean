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
import Theorem.v1.Atlas.NumberTheoryI.code.ConductorOrders


noncomputable section

open Ideal Polynomial Algebra IsDedekindDomain nonZeroDivisors

section ConductorFiniteness

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

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

end ConductorFiniteness
end

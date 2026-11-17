/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ConductorOrders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.RingTheory.Conductor
public import Mathlib.NumberTheory.KummerDedekind
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.Algebra.Module.Lattice
public import Mathlib.Tactic.LinearCombination
public import Class.v1.Atlas.NumberTheoryI.code.ConductorOrders

public section

noncomputable section

open Ideal Polynomial Algebra IsDedekindDomain nonZeroDivisors

section ConductorFiniteness

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

omit [IsDomain A] in
lemma nonZeroDivisors_le_comap_atPrime (𝔭 : Ideal A) [𝔭.IsPrime] :
    A⁰ ≤ Submonoid.comap (algebraMap A (Localization.AtPrime 𝔭)) (Localization.AtPrime 𝔭)⁰ := by
  intro a ha
  rw [Submonoid.mem_comap]
  exact IsLocalization.map_nonZeroDivisors_le 𝔭.primeCompl (Localization.AtPrime 𝔭) ⟨a, ha, rfl⟩


end ConductorFiniteness
end

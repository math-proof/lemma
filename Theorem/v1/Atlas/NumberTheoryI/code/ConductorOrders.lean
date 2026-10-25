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
import Class.v1.Atlas.NumberTheoryI.code.ConductorOrders


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

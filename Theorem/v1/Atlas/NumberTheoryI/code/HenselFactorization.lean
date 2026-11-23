/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Instance.v1.Atlas.NumberTheoryI.code.HenselLemmas
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.HenselLemmas
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.ScalingStep
public import Instance.v1.Atlas.NumberTheoryI.code.ScalingStep
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Norm.Transitivity
open Polynomial IsLocalRing

public section

section HenselIII

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

end HenselIII


section HenselKurschak

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

theorem isLocalRing_of_unique_maximal (R : Type*) [CommRing R] [IsDomain R]
    (𝔮 : Ideal R) (h𝔮 : 𝔮.IsMaximal)
    (huniq : ∀ (I : Ideal R), I.IsMaximal → I = 𝔮) : IsLocalRing R :=
  IsLocalRing.of_is_unit_or_is_unit_of_add_one (fun {a b} hab => by
    by_cases ha : a ∈ 𝔮
    · right
      have hb : b ∉ 𝔮 := fun hb =>
        h𝔮.ne_top ((Ideal.eq_top_iff_one 𝔮).mpr (hab ▸ 𝔮.add_mem ha hb))
      rw [← Ideal.span_singleton_eq_top]
      by_contra h
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
      exact hb (huniq M hM ▸ hle (Ideal.subset_span rfl))
    · left
      rw [← Ideal.span_singleton_eq_top]
      by_contra h
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
      exact ha (huniq M hM ▸ hle (Ideal.subset_span rfl)))

end HenselKurschak

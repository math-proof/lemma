/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.NumberTheoryI.code.HenselLemmas
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselLemmas
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ScalingStep
import Instance.v1.Atlas.NumberTheoryI.code.ScalingStep
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
open Polynomial IsLocalRing


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

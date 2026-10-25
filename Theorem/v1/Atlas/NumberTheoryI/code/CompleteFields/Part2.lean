/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CompleteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Over
import Def.v1.Atlas.NumberTheoryI.code.Chapter1.AbsoluteValues.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Chapter1.AbsoluteValues
import Def.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2


noncomputable section

open scoped Topology

open UniformSpace

set_option maxHeartbeats 800000 in
lemma intValuation_algebraMap_eq
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]
    (P : HeightOneSpectrum R) (Q : HeightOneSpectrum S) [Q.asIdeal.LiesOver P.asIdeal]
    (r : R) :
    Q.intValuation (algebraMap R S r) =
      (P.intValuation r) ^ (Ideal.ramificationIdx P.asIdeal Q.asIdeal) := by
  classical
  by_cases hr : r = 0
  · subst hr
    simp only [map_zero]
    have he : Ideal.ramificationIdx P.asIdeal Q.asIdeal ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver Q.asIdeal P.ne_bot
    exact (zero_pow he).symm
  have hsr : algebraMap R S r ≠ 0 := by
    intro h
    exact hr (FaithfulSMul.algebraMap_injective R S (h.trans (map_zero _).symm))
  rw [Q.intValuation_if_neg hsr, P.intValuation_if_neg hr]
  rw [show Ideal.span {algebraMap R S r} = Ideal.map (algebraMap R S) (Ideal.span {r}) from
    by rw [Ideal.map_span, Set.image_singleton]]
  have hspan_ne : (Ideal.span {r} : Ideal R) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr
  have hmap_ne : Ideal.map (algebraMap R S) (Ideal.span {r}) ≠ 0 := by
    rw [ne_eq, Ideal.zero_eq_bot]
    exact Ideal.map_ne_bot_of_ne_bot (by rwa [ne_eq, Ideal.span_singleton_eq_bot])
  rw [count_associates_factors_eq hmap_ne Q.isPrime Q.ne_bot,
      count_associates_factors_eq hspan_ne P.isPrime P.ne_bot]
  have hPirr : Irreducible P.asIdeal := P.irreducible
  have hQirr : Irreducible Q.asIdeal := Q.irreducible
  set n := Multiset.count P.asIdeal
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {r}))
  set e := Ideal.ramificationIdx P.asIdeal Q.asIdeal
  have hcount : Multiset.count Q.asIdeal (UniqueFactorizationMonoid.normalizedFactors
      (Ideal.map (algebraMap R S) (Ideal.span {r}))) = e * n := by
    have h1 : emultiplicity Q.asIdeal (Ideal.map (algebraMap R S) (Ideal.span {r})) =
        ↑e * emultiplicity P.asIdeal (Ideal.span {r}) :=
      Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul
        (by rwa [ne_eq, ← Ideal.zero_eq_bot]) hPirr hQirr Q.ne_bot
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hQirr
          (by rwa [ne_eq, ← Ideal.zero_eq_bot] :
            Ideal.map (algebraMap R S) (Ideal.span {r}) ≠ ⊥),
        normalize_eq] at h1
    rw [UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hPirr
          (by rwa [ne_eq, ← Ideal.zero_eq_bot] : (Ideal.span {r} : Ideal R) ≠ ⊥),
        normalize_eq] at h1
    exact_mod_cast h1
  rw [hcount]
  rw [WithZero.exp, WithZero.exp, ← zpow_natCast, ← WithZero.coe_zpow, WithZero.coe_inj,
      ← ofAdd_zsmul]
  congr 1; push_cast; ring

set_option maxHeartbeats 800000 in
theorem valuation_extends_with_ramificationIdx
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra R S] [FaithfulSMul R S]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]
    [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]
    (P : HeightOneSpectrum R) (Q : HeightOneSpectrum S) [Q.asIdeal.LiesOver P.asIdeal]
    (x : K) :
    Q.valuation L (algebraMap K L x) =
      (P.valuation K x) ^ (Ideal.ramificationIdx P.asIdeal Q.asIdeal) := by
  obtain ⟨⟨a, ⟨b, hb⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  simp only
  rw [P.valuation_of_mk', IsFractionRing.mk'_eq_div, map_div₀, Valuation.map_div]
  have ha' : algebraMap K L (algebraMap R K a) = algebraMap R L a :=
    (IsScalarTower.algebraMap_apply R K L a).symm
  have hb' : algebraMap K L (algebraMap R K b) = algebraMap R L b :=
    (IsScalarTower.algebraMap_apply R K L b).symm
  rw [ha', hb']
  rw [show algebraMap R L a = algebraMap S L (algebraMap R S a) from
        IsScalarTower.algebraMap_apply R S L a,
      show algebraMap R L b = algebraMap S L (algebraMap R S b) from
        IsScalarTower.algebraMap_apply R S L b]
  rw [Q.valuation_of_algebraMap, Q.valuation_of_algebraMap]
  rw [intValuation_algebraMap_eq P Q, intValuation_algebraMap_eq P Q]
  show (P.intValuation a) ^ _ / (P.intValuation b) ^ _ = _
  rw [div_pow]

end

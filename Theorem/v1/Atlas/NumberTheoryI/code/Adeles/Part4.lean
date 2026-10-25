/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part5


noncomputable section

open NumberField IsDedekindDomain

open scoped TensorProduct

namespace NumberField.Adeles

variable {K : Type*} [Field K] [NumberField K]

section RestrictedProductDirectLimit

open Filter Set Topology

attribute [local instance] WithAbs.algebraLeft

lemma baseChangeAtPrime_mem_integers (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (w : HeightOneSpectrum (𝓞 L))
    (x : (primeBelow K L w).adicCompletion K)
    (hx : x ∈ (primeBelow K L w).adicCompletionIntegers K) :
    (baseChangeAtPrime K L w) x ∈ w.adicCompletionIntegers L := by

  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx


  have hclosed : IsClosed {y : (primeBelow K L w).adicCompletion K |
      Valued.v y ≤ 1 → Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} := by
    have h1 : {y : (primeBelow K L w).adicCompletion K |
        Valued.v y ≤ 1 → Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} =
        {y | ¬(Valued.v y ≤ 1)} ∪ {y | Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} := by
      ext y; simp only [Set.mem_setOf_eq, Set.mem_union]; tauto
    rw [h1]
    apply IsClosed.union
    ·
      have : {y : (primeBelow K L w).adicCompletion K | ¬(Valued.v y ≤ 1)} =
          ((Valued.v.valuationSubring :
            ValuationSubring ((primeBelow K L w).adicCompletion K)) :
            Set ((primeBelow K L w).adicCompletion K))ᶜ := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_compl_iff, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClopen_valuationSubring
        ((primeBelow K L w).adicCompletion K)).2.isClosed_compl
    ·
      have hf_cont : Continuous (baseChangeAtPrime K L w) :=
        UniformSpace.Completion.continuous_extension
      have : {y : (primeBelow K L w).adicCompletion K |
          Valued.v ((baseChangeAtPrime K L w) y) ≤ 1} =
          (baseChangeAtPrime K L w :
            (primeBelow K L w).adicCompletion K → w.adicCompletion L) ⁻¹'
            ((Valued.v.valuationSubring : ValuationSubring (w.adicCompletion L)) :
              Set (w.adicCompletion L)) := by
        ext y; simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
          Valuation.mem_valuationSubring_iff]
      rw [this]
      exact (Valued.isClosed_valuationSubring (w.adicCompletion L)).preimage hf_cont

  have hdense : ∀ (k : WithVal (HeightOneSpectrum.valuation K (primeBelow K L w))),
      Valued.v (↑k : (primeBelow K L w).adicCompletion K) ≤ 1 →
        Valued.v ((baseChangeAtPrime K L w) (↑k : (primeBelow K L w).adicCompletion K)) ≤ 1 := by
    intro k hk
    rw [Valued.valuedCompletion_apply] at hk

    have hf_coe : (baseChangeAtPrime K L w) (↑k : (primeBelow K L w).adicCompletion K) =
        localBaseChangeMap K L w k :=
      UniformSpace.Completion.extensionHom_coe _ (localBaseChangeMap_continuous K L w) k
    rw [hf_coe]


    have hval : Valued.v ((localBaseChangeMap K L w) k) =
        HeightOneSpectrum.valuation L w (algebraMap K L
          ((WithVal.equiv (HeightOneSpectrum.valuation K (primeBelow K L w))) k)) := by
      simp only [localBaseChangeMap, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
      erw [Valued.valuedCompletion_apply]
      rw [← WithVal.val_apply_equiv (HeightOneSpectrum.valuation L w)]
      simp only [RingEquiv.apply_symm_apply]
    rw [hval]


    haveI : w.asIdeal.LiesOver (primeBelow K L w).asIdeal := ⟨rfl⟩
    rw [valuation_extends_with_ramificationIdx K L (primeBelow K L w) w]
    rw [WithVal.val_apply_equiv]
    exact pow_le_one₀ (WithZero.zero_le _) hk


  exact UniformSpace.Completion.induction_on x hclosed (fun k => hdense k) hx

lemma baseChange_restricted_condition (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (a : FiniteAdeleRing (𝓞 K) K) :
    ∀ᶠ (w : HeightOneSpectrum (𝓞 L)) in Filter.cofinite,
      (baseChangeAtPrime K L w) (a (primeBelow K L w)) ∈
        ↑(w.adicCompletionIntegers L) := by


  have ha := a.property

  rw [Filter.eventually_cofinite] at ha ⊢


  set S := {v : HeightOneSpectrum (𝓞 K) | a v ∉ (v.adicCompletionIntegers K : Set (v.adicCompletion K))} with hS_def

  apply Set.Finite.subset (s := primeBelow K L ⁻¹' S)
  ·


    have hS_eq : primeBelow K L ⁻¹' S = ⋃ v ∈ S, {w | primeBelow K L w = v} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨primeBelow K L w, h, rfl⟩, fun ⟨v, hv, hvw⟩ => hvw ▸ hv⟩
    rw [hS_eq]
    apply ha.biUnion
    intro v _


    have hinj : Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 L)) :=
      fun a b h => HeightOneSpectrum.ext_iff.mpr h
    apply Set.Finite.subset ((primesOver_finite v.asIdeal (𝓞 L)).preimage hinj.injOn)
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hw ⊢
    refine ⟨w.isPrime, ⟨?_⟩⟩
    show v.asIdeal = Ideal.under (𝓞 K) w.asIdeal
    rw [Ideal.under, ← hw]
    rfl

  ·
    intro w hw
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS_def] at hw ⊢


    intro hmem
    exact hw (baseChangeAtPrime_mem_integers K L w _ hmem)

lemma baseChange_commutes (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (k : K) :
    (RestrictedProduct.mk
      (fun w => (baseChangeAtPrime K L w)
        ((algebraMap K (FiniteAdeleRing (𝓞 K) K) k) (primeBelow K L w)))
      (baseChange_restricted_condition K L (algebraMap K (FiniteAdeleRing (𝓞 K) K) k))) =
    algebraMap K (FiniteAdeleRing (𝓞 L) L) k := by
  apply RestrictedProduct.ext; intro w
  simp only [RestrictedProduct.mk_apply]

  have hLHS : ((algebraMap K (FiniteAdeleRing (𝓞 K) K)) k) (primeBelow K L w) =
    (algebraMap K ((primeBelow K L w).adicCompletion K) k) := rfl
  rw [hLHS]

  simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp]

  simp only [baseChangeAtPrime, UniformSpace.Completion.extensionHom_coe]

  simp only [localBaseChangeMap, RingHom.comp_apply]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rfl

end RestrictedProductDirectLimit
end NumberField.Adeles
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part8
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GroupCounts
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeberLocal2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.ResidueFieldHelper
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CyclotomicDVRInstances
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.KroneckerWeberLocal2.Part2
import Theorem.v1.Atlas.NumberTheoryI.code.ResidueFieldHelper
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Instance.v1.Atlas.NumberTheoryI.code.CyclotomicDVRInstances
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part3


noncomputable section

namespace KroneckerWeber

theorem ps5_galois_cyclic_quartic_bound
    (K : Type) [Field K] [Algebra ℚ_[2] K]
    [FiniteDimensional ℚ_[2] K] [IsGalois ℚ_[2] K] :
    Nat.card {H : Subgroup (K ≃ₐ[ℚ_[2]] K) //
      H.index = 4 ∧ ∃ (_ : H.Normal), IsCyclic ((K ≃ₐ[ℚ_[2]] K) ⧸ H)} ≤ 12 := by
  haveI : Finite (IntermediateField ℚ_[2] K) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ_[2] K
      (Field.exists_primitive_element ℚ_[2] K)
  apply le_trans _ (KroneckerWeberLocal2.ps5_at_most_12_cyclic_quartic_extensions K)
  apply Nat.card_le_card_of_injective
    (fun x => ⟨IntermediateField.fixedField x.1, by
      obtain ⟨H, hindex, hexists⟩ := x
      haveI : H.Normal := hexists.choose
      refine ⟨?_, ?_, ?_⟩
      · rw [IntermediateField.finrank_eq_fixingSubgroup_index,
            @IntermediateField.fixingSubgroup_fixedField ℚ_[2] _ K _ _ H _]
        exact hindex
      · exact IsGalois.of_fixedField_normal_subgroup H
      · exact (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient H)).mp hexists.choose_spec⟩)
  intro ⟨H1, _⟩ ⟨H2, _⟩ heq
  simp only [Subtype.mk.injEq] at heq ⊢
  have : (IntermediateField.fixedField H1).fixingSubgroup =
         (IntermediateField.fixedField H2).fixingSubgroup := by rw [heq]
  rwa [IntermediateField.fixingSubgroup_fixedField,
       IntermediateField.fixingSubgroup_fixedField] at this

theorem Z4Z3_cyclic_quartic_count_with_normal :
    Nat.card {H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) //
      H.index = 4 ∧ ∃ (_ : H.Normal),
        IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)} = 28 := by
  rw [show (fun H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) =>
      H.index = 4 ∧ ∃ (_ : H.Normal),
        IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)) =
    (fun H => H.index = 4 ∧
        IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)) from by
    ext H; constructor
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, Subgroup.normal_of_comm H, h2⟩]
  exact GroupCounts.Z4Z3_cyclic_quartic_count

theorem cyclic_normal_index_subgroups_card_eq_of_mulEquiv
    {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G ⧸ H)} =
    Nat.card {H : Subgroup G' // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G' ⧸ H)} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := by
      change (H.map φ.toMonoidHom).Normal
      exact Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
    refine ⟨?_, h_norm', ?_⟩
    · change (H.map (φ : G →* G')).index = n
      rw [Subgroup.index_map_equiv H φ]; exact h_idx
    · haveI : (H.map φ.toMonoidHom).Normal :=
        Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
      haveI := h_norm
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mp h_cyc

  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := h_norm
    haveI : (φ.mapSubgroup.toEquiv H).Normal := h_norm
    haveI : (H.map (φ : G →* G')).Normal := ‹_›
    have h_normH : H.Normal := by
      have heq : H = (H.map (φ : G →* G')).comap (φ : G →* G') := by
        ext x; constructor
        · intro hx; exact ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, he⟩; exact φ.injective he ▸ hy
      rw [heq]; exact Subgroup.Normal.comap ‹(H.map (φ : G →* G')).Normal› _
    refine ⟨?_, h_normH, ?_⟩
    · change (H.map (φ : G →* G')).index = n at h_idx
      rw [Subgroup.index_map_equiv H φ] at h_idx; exact h_idx
    · haveI := h_normH
      haveI : (H.map φ.toMonoidHom).Normal := ‹(H.map (φ : G →* G')).Normal›
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mpr h_cyc

theorem lemma_20_11_no_Z4Z3 :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) := by
  intro ⟨K, hK_field, hK_alg, hK_fd, hK_gal, ⟨φ⟩⟩

  have h_bound := ps5_galois_cyclic_quartic_bound K

  rw [cyclic_normal_index_subgroups_card_eq_of_mulEquiv φ] at h_bound

  rw [Z4Z3_cyclic_quartic_count_with_normal] at h_bound

  omega

theorem lemma_20_11 :
    (¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2))) ∧
    (¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 4 × ZMod 4 × ZMod 4))) :=
  ⟨lemma_20_11_no_Z2Z4, lemma_20_11_no_Z4Z3⟩

end KroneckerWeber
end

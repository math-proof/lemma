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
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part2


noncomputable section

namespace KroneckerWeber

lemma index_map_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (H : Subgroup G) :
    (H.map φ.toMonoidHom).index = H.index := by
  apply Subgroup.index_map_eq
  · exact φ.surjective
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := φ.injective (hx.trans (map_one φ).symm)
    rw [this]; exact H.one_mem

lemma index_subgroups_card_eq_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n} =
      Nat.card {H : Subgroup G' // H.index = n} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · intro h
    change (φ.mapSubgroup H).index = n
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl]
    rw [index_map_mulEquiv]; exact h
  · intro h
    have : (φ.mapSubgroup H).index = n := h
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl] at this
    rw [index_map_mulEquiv] at this; exact this

theorem ps4_galois_index2_bound
    (K : Type) [Field K] [Algebra ℚ_[2] K]
    [FiniteDimensional ℚ_[2] K] [IsGalois ℚ_[2] K] :
    Nat.card {H : Subgroup (K ≃ₐ[ℚ_[2]] K) // H.index = 2} ≤ 7 := by
  rw [Nat.card_congr (KroneckerWeberLocal2.galoisCorrespondenceIndex ℚ_[2] K 2)]
  exact KroneckerWeberLocal2.ps4_at_most_7_quadratic_extensions K

theorem Z2Z4_index2_count :
    Nat.card {H : Subgroup (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) //
      H.index = 2} = 15 :=
  GroupCounts.Z2Z4_index2_count

theorem lemma_20_11_no_Z2Z4 :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) := by
  intro ⟨K, hK_field, hK_alg, hK_fd, hK_gal, ⟨φ⟩⟩
  have h_bound := ps4_galois_index2_bound K
  rw [index_subgroups_card_eq_of_mulEquiv φ 2, Z2Z4_index2_count] at h_bound
  omega

end KroneckerWeber
end

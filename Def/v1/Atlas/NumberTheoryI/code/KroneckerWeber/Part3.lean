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
import Theorem.v1.Atlas.NumberTheoryI.code.KroneckerWeber


noncomputable section

namespace KroneckerWeber

noncomputable def galoisCorrespondenceIndex (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (n : ℕ) :
    {H : Subgroup (K ≃ₐ[F] K) // H.index = n} ≃
    {L : IntermediateField F K // Module.finrank F L = n} where
  toFun := fun ⟨H, hH⟩ => ⟨IntermediateField.fixedField H, by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
        @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _]
    exact hH⟩
  invFun := fun ⟨L, hL⟩ => ⟨L.fixingSubgroup, by
    rwa [← IntermediateField.finrank_eq_fixingSubgroup_index]⟩
  left_inv := fun ⟨H, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _
  right_inv := fun ⟨L, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact IsGalois.fixedField_fixingSubgroup L

end KroneckerWeber
end

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
import Theorem.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part2


noncomputable section

namespace KroneckerWeber

noncomputable def adicCompletionTensorLift
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum A)
    (𝔮 : IsDedekindDomain.HeightOneSpectrum B)
    [Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K (𝔭.adicCompletion K) (𝔮.adicCompletion L)]
    [IsScalarTower K L (𝔮.adicCompletion L)] :
    TensorProduct K (𝔭.adicCompletion K) L →ₐ[𝔭.adicCompletion K] 𝔮.adicCompletion L :=
  Algebra.TensorProduct.lift
    (Algebra.ofId (𝔭.adicCompletion K) (𝔮.adicCompletion L))
    (IsScalarTower.toAlgHom K L (𝔮.adicCompletion L))
    (fun _ _ => mul_comm _ _)


section

set_option synthInstance.maxHeartbeats 400000

noncomputable def completion_residueFieldEquiv
    (A : Type u_A₈') [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type u_K₈') [Field K] [Algebra A K] [IsFractionRing A K]
    (𝔭 : HeightOneSpectrum A) :
    (↥(𝔭.adicCompletionIntegers K) ⧸
      IsLocalRing.maximalIdeal ↥(𝔭.adicCompletionIntegers K)) ≃+*
    (A ⧸ 𝔭.asIdeal) :=
  (RingHom.quotientKerEquivOfSurjective
    (𝔭.surj_completionResidueMap (K := K))).symm.trans
    (Ideal.quotEquivOfEq (𝔭.ker_completionResidueMap (K := K)))

end
end KroneckerWeber
end

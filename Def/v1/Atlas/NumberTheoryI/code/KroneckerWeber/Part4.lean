module
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Finiteness
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Theorem.v1.Atlas.NumberTheoryI.code.GroupCounts.Part8
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.GroupCounts
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeberLocal2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.ResidueFieldHelper
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.CyclotomicDVRInstances
public import Mathlib.RingTheory.Valuation.Extension
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.KroneckerWeberLocal2.Part2
public import Theorem.v1.Atlas.NumberTheoryI.code.ResidueFieldHelper
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.RootsOfUnity.Lemmas
public import Instance.v1.Atlas.NumberTheoryI.code.CyclotomicDVRInstances
public import Theorem.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/KroneckerWeber.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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

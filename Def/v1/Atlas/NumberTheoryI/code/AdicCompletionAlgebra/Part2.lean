module
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Ideal.IntegralClosure
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.Over
public import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part2
open IsDedekindDomain UniformSpace
set_option maxHeartbeats 800000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AdicCompletionAlgebra.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
@[reducible]
noncomputable def instAlgebraAdicCompletionOfLiesOver
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    Algebra (𝔭.adicCompletion K) (𝔮.adicCompletion L) :=
  (AdicCompletionAlgebra.adicCompletionMap K 𝔭 𝔮 h𝔮_over_𝔭).toAlgebra

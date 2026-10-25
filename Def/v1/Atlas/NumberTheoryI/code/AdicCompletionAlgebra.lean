/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AdicCompletionAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Ideal.Over
import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra
open IsDedekindDomain UniformSpace

set_option maxHeartbeats 800000


namespace AdicCompletionAlgebra

noncomputable def adicCompletionMap
    {A : Type*} [CommRing A] [IsDedekindDomain A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsFractionRing B L]
    (𝔭 : HeightOneSpectrum A)
    (𝔮 : HeightOneSpectrum B)
    (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
    𝔭.adicCompletion K →+* 𝔮.adicCompletion L :=
  Completion.extensionHom
    ((algebraMap L (𝔮.adicCompletion L)).comp
      ((algebraMap K L).comp (WithVal.equiv (𝔭.valuation K)).toRingHom))
    (continuous_algebraMap_adicCompletion K 𝔭 𝔮 h𝔮_over_𝔭)

end AdicCompletionAlgebra

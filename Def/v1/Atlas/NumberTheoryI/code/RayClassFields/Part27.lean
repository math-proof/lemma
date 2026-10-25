/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
import Instance.v1.Atlas.NumberTheoryI.code.RayClassFields.Part11


noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

attribute [instance] instFintypeSignsTimesUnits

attribute [instance] instFintypeRayClassGroup

noncomputable def PolarDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) : Option ℚ :=
  open Classical in
  if h : ∃ ρ : ℚ, HasPolarDensity K S ρ then some h.choose else none

noncomputable def DirichletDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) : Option ℚ :=
  open Classical in
  if h : ∃ ρ : ℚ, HasDirichletDensity K S ρ then some h.choose else none

noncomputable def NaturalDensity (K : Type*) [Field K] [NumberField K]
    (S : Set (Prime' K)) : Option ℚ :=
  open Classical in
  if h : ∃ ρ : ℚ, HasNaturalDensity K S ρ then some h.choose else none

def IsDegreeOne (𝔭 : Prime' K) : Prop :=
  Nat.Prime (Ideal.absNorm 𝔭.asIdeal)

def SplitsCompletely (K L : Type u) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Prime' K) : Prop :=
  FrobeniusAutomorphism K L 𝔭 = 1

def Spl (K L : Type u) [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [IsGalois K L] : Set (Prime' K) :=
  {𝔭 | SplitsCompletely K L 𝔭}

def SplitsCompletelyGen (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)),
    𝔔.asIdeal.LiesOver 𝔭.asIdeal →
    𝔭.asIdeal.ramificationIdx 𝔔.asIdeal = 1 ∧ 𝔭.asIdeal.inertiaDeg 𝔔.asIdeal = 1

def SplGen (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] : Set (Prime' K) :=
  {𝔭 | SplitsCompletelyGen K L 𝔭}


def FinSymmDiff (S T : Set (Prime' K)) : Prop :=
  Set.Finite (symmDiff S T)

def PrimeSetLe (S T : Set (Prime' K)) : Prop :=
  Set.Finite (S \ T)

end RayClassField
end

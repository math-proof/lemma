/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalCFT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part28
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ideles
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdeleNorm
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor227
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22NormGroup
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Prop2219
import Def.v1.Atlas.NumberTheoryI.code.Ideles.Part3
import Def.v1.Atlas.NumberTheoryI.code.IdeleNorm.Part4
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Theorem.v1.Atlas.NumberTheoryI.code.Cor227.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Chapter3.FiniteApproximation
import Theorem.v1.Atlas.NumberTheoryI.code.Ch22NormGroup.Part4
import Def.v1.Atlas.NumberTheoryI.code.Prop2219.Part2
import Theorem.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part6


noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

noncomputable def extensionConductor (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Modulus K :=
  conductorOfCongruenceSubgroup K
    (extensionAdmissibleModulus K L)
    (extensionNormSubgroup K L)
    (extensionNormSubgroup_isCong K L)

def IsUnramifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) 𝔔

def IsTamelyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
      ¬ (ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) ∣
          Ideal.ramificationIdx 𝔭.asIdeal 𝔔)

def IsWildlyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∃ (𝔔 : Ideal (NumberField.RingOfIntegers L)) (_ : 𝔔.IsPrime),
    𝔔.LiesOver 𝔭.asIdeal ∧
      ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) ∣
        Ideal.ramificationIdx 𝔭.asIdeal 𝔔

def IsTotallyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
      Ideal.inertiaDeg 𝔭.asIdeal 𝔔 = 1

def IsTotallyTamelyRamified (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  IsTotallyRamifiedIn K L 𝔭 ∧ IsTamelyRamifiedIn K L 𝔭

def IsTotallyWildlyRamified (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  IsTotallyRamifiedIn K L 𝔭 ∧
    ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
      𝔔.LiesOver 𝔭.asIdeal →
        ∃ k : ℕ, Ideal.ramificationIdx 𝔭.asIdeal 𝔔 =
          (ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal)) ^ k

noncomputable def NormGroup (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K) : Subgroup (FracIdealsCoprime K 𝔪) :=
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
  letI : NumberField L := NumberField.mk

  RayClassField.NormGroup K L 𝔪

noncomputable def choosePrimeOverHOS (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prime' L :=
  ⟨choosePrimeOver K L 𝔭, choosePrimeOver_isPrime K L 𝔭, choosePrimeOver_ne_bot K L 𝔭⟩

end ArtinSymbol
end

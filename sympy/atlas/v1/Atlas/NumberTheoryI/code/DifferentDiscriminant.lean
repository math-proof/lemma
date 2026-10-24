/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import sympy.atlas.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.EtaleAlgebrasProps
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealNorms
import sympy.atlas.v1.Atlas.NumberTheoryI.code.IdealNorms

noncomputable section

open Algebra Submodule FractionalIdeal
open scoped Matrix

universe u

section TraceDualBModule

variable {A K : Type*} {L : Type u} {B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

def traceDualB : FractionalIdeal (nonZeroDivisors B) L :=
  FractionalIdeal.dual A K 1

abbrev different : Ideal B := differentIdeal A B

def disc (x : Fin n → S) : R := Algebra.discr R x

open Polynomial in
def polyDiscr (f : R[X]) : R := f.discr

def latticeDiscrSet (M : Submodule A L) : Set K :=
  { d : K | ∃ b : Fin (Module.finrank K L) → L,
      (∀ i, b i ∈ M) ∧ d = Algebra.discr K b }

def latticeDiscriminant (M : Submodule A L) : Submodule A K :=
  Submodule.span A (latticeDiscrSet A K M)

set_option linter.unusedSectionVars false in

open Classical in
def elementDifferent (α : L) : L :=
  if IntermediateField.adjoin K {α} = ⊤
  then Polynomial.aeval α (Polynomial.derivative (minpoly K α))
  else 0

def elementDifferentB (α : B) : B := by
  classical
  exact if Algebra.adjoin K {algebraMap B L α} = ⊤
    then Polynomial.aeval α (Polynomial.derivative (minpoly A α))
    else 0

def idealValuation (𝔮 : HeightOneSpectrum B) (I : Ideal B) : ℕ :=
  multiplicity 𝔮.asIdeal I

def ramificationIndex (𝔮 : HeightOneSpectrum B) : ℕ :=
  Ideal.ramificationIdx (𝔮.asIdeal.comap (algebraMap A B)) 𝔮.asIdeal

def IsTamelyRamified (𝔮 : HeightOneSpectrum B) : Prop :=
  ¬ (ringChar (B ⧸ 𝔮.asIdeal) ∣ ramificationIndex A B 𝔮)

def valuationOfRamIdx (𝔮 : HeightOneSpectrum B) : ℕ :=
  idealValuation B 𝔮 (Ideal.span {(ramificationIndex A B 𝔮 : B)})

def imageOfB : Submodule A L :=
  Subalgebra.toSubmodule (IsScalarTower.toAlgHom A B L).range

instance imageOfB_finite [Module.Finite A B] : Module.Finite A ↥(imageOfB A L B) := by
  have : Module.Finite A ((IsScalarTower.toAlgHom A B L).toLinearMap.range) :=
    Module.Finite.range (IsScalarTower.toAlgHom A B L).toLinearMap
  convert this

def extensionDiscriminant : Submodule A K :=
  latticeDiscriminant A K (imageOfB A L B)


def discriminantBaseChange : Submodule Ahat Khat :=
  Submodule.span Ahat (algebraMap K Khat '' (extensionDiscriminant A K L B : Set K))

end DiscriminantCompletion

section DiscriminantNormDifferent


variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsDomain A] [IsFractionRing A K] [IsIntegrallyClosed A]
  [FiniteDimensional K L] [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsFractionRing B L] [Nontrivial B] [NoZeroDivisors B]
  [IsDedekindDomain A] [IsDedekindDomain B]

  [Module.Finite A B] [Module.IsTorsionFree A B]

def subalgebraConductor {A : Type*} {B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (𝒪 : Subalgebra A B) : Ideal B where
  carrier := {a | ∀ b : B, a * b ∈ 𝒪}
  zero_mem' b := by simp
  add_mem' ha hb c := by simpa [add_mul] using 𝒪.add_mem (ha c) (hb c)
  smul_mem' c a ha b := by simpa [mul_left_comm, mul_assoc] using ha (c * b)

def imageOfSubalgebra (𝒪 : Subalgebra A B) : Submodule A L :=
  Submodule.map (IsScalarTower.toAlgHom A B L).toLinearMap 𝒪.toSubmodule

def orderDiscriminant (𝒪 : Subalgebra A B) : Submodule A K :=
  latticeDiscriminant A K (imageOfSubalgebra A L B 𝒪)

end OrderDiscriminant

end

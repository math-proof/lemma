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
import Instance.v1.Atlas.NumberTheoryI.code.EtaleAlgebrasProps
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.EtaleAlgebrasProps
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.IdealNorms
import Def.v1.Atlas.NumberTheoryI.code.IdealNorms
import Abbrev.v1.Atlas.NumberTheoryI.code.DifferentDiscriminant


noncomputable section

open Algebra Submodule FractionalIdeal

open scoped Matrix

universe u

section TraceDualBModule

variable {A K : Type*} {L : Type u} {B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

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

end TraceDualBModule
end

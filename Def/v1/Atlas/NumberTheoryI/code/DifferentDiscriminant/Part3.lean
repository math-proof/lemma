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
import Instance.v1.Atlas.NumberTheoryI.code.DifferentDiscriminant


noncomputable section

open Algebra Submodule FractionalIdeal

open scoped Matrix

universe u

section TraceDualBModule

variable {A K : Type*} {L : Type u} {B : Type*}
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]

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

end DiscriminantNormDifferent
end

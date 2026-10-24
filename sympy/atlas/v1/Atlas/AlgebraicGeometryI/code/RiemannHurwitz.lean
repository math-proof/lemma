/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Algebraic.Integral
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.FiniteMorphismDimension
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral

noncomputable section

open Ideal Module

section FundamentalIdentity

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  (K L : Type*) [Field K] [Field L]
  [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [IsFractionRing S L]
  [Algebra K L] [Algebra R L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [Module.Finite R S]

/-- Abbreviation for `Algebra.IsUnramifiedAt R P`, naming the property that an
algebra `R → S` is unramified at the prime `P` of `S` lying over `p`. -/
abbrev IsUnramifiedAt' (p : Ideal R) (P : Ideal S) [P.IsPrime] [P.LiesOver p] : Prop :=
  Algebra.IsUnramifiedAt R P

/-- `R → S` is unramified over `p` if it is unramified at every prime `P`
of `S` lying over `p`. -/
def IsUnramifiedOver (p : Ideal R) : Prop :=
  ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p], Algebra.IsUnramifiedAt R P

/-- Every prime ideal `P` of `S` lies over its contraction `P ∩ R`. -/
instance dedekind_liesOver_contraction
    (R S : Type*) [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S]
    [Algebra R S]
    (P : Ideal S) :
    P.LiesOver (P.under R) :=
  Ideal.over_under P

end Chevalley

section RamificationDivisor

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]

/-- Local contribution at `p` to the ramification divisor: the sum
`∑_{P|p} (e_P - 1)`. -/
def totalRamificationAt
    {R : Type*} [CommRing R] [IsDedekindDomain R]
    (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
    [NoZeroSMulDivisors R S]
    (p : Ideal R) [p.IsMaximal] (_hp0 : p ≠ ⊥) : ℤ :=
  ∑ P ∈ primesOverFinset p S,
    ((p.ramificationIdx P : ℤ) - 1)

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 * (2 - 1) := by norm_num

example : (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 * (2 - 1) := by norm_num

example : (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

end RiemannHurwitzFormula

end

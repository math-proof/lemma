/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Algebraic.Integral
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.NakayamaApplications
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.FiniteMorphismDimension
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral


@[expose] public noncomputable section

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

end FundamentalIdentity
end

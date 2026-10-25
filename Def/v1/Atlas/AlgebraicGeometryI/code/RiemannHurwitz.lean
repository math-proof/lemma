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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.FiniteMorphismDimension
import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRochGeneral
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitz


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

/-- `R → S` is unramified over `p` if it is unramified at every prime `P`
of `S` lying over `p`. -/
def IsUnramifiedOver (p : Ideal R) : Prop :=
  ∀ (P : Ideal S) [P.IsPrime] [P.LiesOver p], Algebra.IsUnramifiedAt R P

end FundamentalIdentity
end

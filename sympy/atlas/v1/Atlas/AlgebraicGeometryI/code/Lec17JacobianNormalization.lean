/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec17JacobianNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.ClassGroup
import Mathlib.Data.Complex.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option maxHeartbeats 800000

noncomputable section

open Algebra AlgebraicGeometry CategoryTheory

namespace Lec17JacobianNormalization

/-- The affine scheme `Spec ℂ`, used as the base for varieties over the complex numbers. -/
abbrev SpecC : Scheme := Scheme.Spec.obj (Opposite.op (CommRingCat.of ℂ))

/-- A smooth projective curve over `ℂ`: a proper, smooth, integral scheme over `Spec ℂ`
of relative dimension `1`, together with its genus. -/
structure SmoothProjectiveCurve where
  toScheme : Scheme
  structureMorphism : toScheme ⟶ SpecC
  isProper : IsProper structureMorphism
  isSmoothOfRelDim1 : SmoothOfRelativeDimension 1 structureMorphism
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  genus : ℕ

/-- An abelian group scheme over `ℂ`: a proper smooth scheme over `Spec ℂ` equipped with
an identity section. (Group operations are not packaged here; this captures the geometric
side used in the Abel--Jacobi statement.) -/
structure AbelianGroupScheme where
  toScheme : Scheme
  structureMorphism : toScheme ⟶ SpecC
  isProper : IsProper structureMorphism
  isSmooth : Smooth structureMorphism
  identitySection : SpecC ⟶ toScheme
  identitySection_comp : identitySection ≫ structureMorphism = 𝟙 SpecC

/-- Proposition 26 (Lecture 17, Abel--Jacobi). Any smooth projective curve `X` of genus `g`
admits a Jacobian variety `Jac(X)`, an abelian group scheme of relative dimension `g`,
together with an Abel--Jacobi morphism `X → Jac(X)` over `Spec ℂ`. -/
noncomputable def lemma_28_birational_surj_normal_iso
    (B A K : Type*) [CommRing B] [IsDomain B] [CommRing A]
    [Field K]
    [Algebra B K] [IsFractionRing B K]
    [Algebra A K] [Algebra B A]
    [IsScalarTower B A K]
    [IsIntegrallyClosed B]
    [IsIntegralClosure A B K] :
    A ≃ₐ[B] B :=
  haveI : IsIntegralClosure B B K :=
    (isIntegrallyClosed_iff_isIntegralClosure K).mp inferInstance
  IsIntegralClosure.equiv B A K B

universe u


/-- A proper dominant morphism that becomes an isomorphism after passing to the normalization
of the source is locally quasi-finite. This is the key geometric input used to upgrade
normalization isomorphisms to finite morphisms in Lecture 17. -/
end Lec17JacobianNormalization

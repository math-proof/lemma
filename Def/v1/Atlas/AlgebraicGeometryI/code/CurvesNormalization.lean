/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CurvesNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
open Algebra


section FiniteBirationalNormal

/-- If `B` is an integrally closed domain with fraction field `K` and `A` is the integral
closure of `B` in `K`, then `A` is algebra-isomorphic to `B` (so a finite birational map
over a normal base is an isomorphism). -/
noncomputable def finite_birational_normal_algEquiv
    (B A K : Type*) [CommRing B] [IsDomain B] [CommRing A]
    [Field K]
    [Algebra B K] [IsFractionRing B K]
    [Algebra A K] [Algebra B A]
    [IsScalarTower B A K]
    [IsIntegrallyClosed B]
    [IsIntegralClosure A B K] :
    A ≃ₐ[B] B :=
  haveI : IsIntegralClosure B B K := (isIntegrallyClosed_iff_isIntegralClosure K).mp inferInstance
  IsIntegralClosure.equiv B A K B

/-- The normalization of an integrally closed domain `A` (its integral closure in its
fraction field) is `A` itself. -/
noncomputable def normalization_of_normal_is_self
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] :
    integralClosure A (FractionRing A) ≃ₐ[A] A := by
  haveI : IsIntegralClosure A A (FractionRing A) :=
    (isIntegrallyClosed_iff_isIntegralClosure (FractionRing A)).mp inferInstance
  letI : Algebra (integralClosure A (FractionRing A)) (FractionRing A) :=
    (integralClosure A (FractionRing A)).val.toRingHom.toAlgebra
  haveI : IsScalarTower A (integralClosure A (FractionRing A)) (FractionRing A) := by
    constructor
    intro x y z
    simp [Algebra.smul_def, mul_assoc]
  exact IsIntegralClosure.equiv A (integralClosure A (FractionRing A)) (FractionRing A) A

end FiniteBirationalNormal

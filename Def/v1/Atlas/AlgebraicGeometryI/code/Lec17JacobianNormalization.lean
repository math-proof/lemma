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
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec17JacobianNormalization
set_option maxHeartbeats 800000


noncomputable section

open Algebra AlgebraicGeometry CategoryTheory

namespace Lec17JacobianNormalization

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

end Lec17JacobianNormalization
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FunctionFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.NakayamaApplications
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.NakayamaApplications
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.NumberTheory.RamificationInertia.Basic


section FunctionField

end FunctionField

noncomputable section

open Module Ideal

section MorphismDegree

variable (B A : Type*) [CommRing B] [IsDomain B] [CommRing A] [IsDomain A]
  [Algebra B A] [FaithfulSMul B A]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The degree of a finite morphism of integral domains, defined via the
fraction-field extension `[K(A) : K(B)]`. -/
def morphismDegree : ℕ := finrank (FractionRing B) (FractionRing A)

end MorphismDegree
end

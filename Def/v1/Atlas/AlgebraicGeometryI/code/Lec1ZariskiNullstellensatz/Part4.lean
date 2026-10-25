/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec1ZariskiNullstellensatz
open MvPolynomial AlgebraicGeometry CategoryTheory


namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- The fundamental Spec-Γ adjunction packaged as a bijection: scheme morphisms
`X → Spec A` correspond to ring maps `A → Γ(X, 𝒪_X)`. -/
noncomputable def affine_variety_yoneda
    (A : CommRingCat) (X : Scheme) :
    (X ⟶ Spec A) ≃ (A ⟶ Γ(X, ⊤)) :=
  (ΓSpec.adjunction.homEquiv X (Opposite.op A)).symm.trans (opEquiv _ _)

end
end Lec1ZariskiNullstellensatz

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec1ZariskiNullstellensatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec1ZariskiNullstellensatz

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory


namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- The Yoneda-style pullback sending a scheme morphism `X → Spec A` to the induced ring map
`A → Γ(X, 𝒪_X)`. -/
def yonedaPullback (A : CommRingCat) (X : Scheme) :
    (X ⟶ Spec A) → (A ⟶ Γ(X, ⊤)) :=
  fun f => ((ΓSpec.adjunction.homEquiv X (Opposite.op A)).symm.trans (opEquiv _ _)) f

end
end Lec1ZariskiNullstellensatz

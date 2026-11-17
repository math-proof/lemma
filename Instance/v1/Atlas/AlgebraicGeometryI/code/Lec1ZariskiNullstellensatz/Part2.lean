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
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec1ZariskiNullstellensatz.Part4

@[expose] public section

open MvPolynomial AlgebraicGeometry CategoryTheory


namespace Lec1ZariskiNullstellensatz

noncomputable section

/-- `Spec A` is an affine scheme. -/
instance spec_isAffine (A : CommRingCat) : IsAffine (Spec A) :=
  AlgebraicGeometry.isAffine_Spec A

end
end Lec1ZariskiNullstellensatz

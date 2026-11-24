module
public import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardProjective
public import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.AdjoinRoot
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.ConicRational


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConicRational.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace ConicRational

section General

variable (R : Type*) [CommRing R]

/-- Over a field, the hyperbola coordinate ring `k[X, X⁻¹]` is an integral domain. -/
noncomputable instance hyperbolaIsDomain :
    IsDomain (AdjoinRoot (hyperbolaPoly k)) := by
  haveI : IsLocalization.Away (Polynomial.X : Polynomial k) (AdjoinRoot (hyperbolaPoly k)) :=
    adjoinRoot_isLocalization (Polynomial k) Polynomial.X
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _ (powers_X_le_nonZeroDivisors k)

end General
end ConicRational

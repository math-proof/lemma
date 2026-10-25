/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ConicRational.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRoch
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.PicardProjective
import Def.v1.Atlas.AlgebraicGeometryI.code.PicardProjective.Part7
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.AdjoinRoot
import Theorem.v1.Atlas.AlgebraicGeometryI.code.ConicRational


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

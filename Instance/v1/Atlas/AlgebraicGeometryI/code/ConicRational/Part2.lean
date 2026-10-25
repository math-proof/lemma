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
import Def.v1.Atlas.AlgebraicGeometryI.code.ConicRational.Part2


namespace ConicRational

section General

variable (R : Type*) [CommRing R]

/-- The hyperbola coordinate ring is the localization of `k[X]` at `X`. -/
instance hyperbolaIsLocalization :
    IsLocalization.Away (Polynomial.X : Polynomial k)
    (AdjoinRoot (hyperbolaPoly k)) :=
  adjoinRoot_isLocalization (Polynomial k) Polynomial.X

end General
end ConicRational

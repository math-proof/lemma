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


namespace ConicRational

section General

variable (R : Type*) [CommRing R]

/-- The polynomial `r·X - 1`, whose root in an extension inverts `r`. -/
noncomputable def invertPoly (r : R) : Polynomial R :=
  Polynomial.C r * Polynomial.X - 1

/-- The localization `R[1/r]` is `R`-algebra isomorphic to `R[X]/(rX - 1)`. -/
noncomputable def localizationEquivAdjoinRoot (r : R) :
    Localization.Away r ≃ₐ[R] AdjoinRoot (invertPoly R r) :=
  Localization.awayEquivAdjoin r

end General
end ConicRational

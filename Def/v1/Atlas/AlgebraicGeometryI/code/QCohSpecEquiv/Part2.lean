/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohSpecEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Instance.v1.Atlas.AlgebraicGeometryI.code.QCohSpecEquiv
open AlgebraicGeometry CategoryTheory


noncomputable section

universe u

variable {R : CommRingCat.{u}}

/-- Equivalence of categories between `Mod R` and the essential image of the
tilde functor, packaging the fully-faithful corestriction. -/
def tildeEssImageEquiv :
    ModuleCat.{u} R ≌ (tilde.functor R).EssImageSubcategory :=
  (tilde.functor R).toEssImage.asEquivalence

end

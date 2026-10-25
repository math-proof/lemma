/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/AffineMorphismEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Instance.v1.Atlas.AlgebraicGeometryI.code.AffineMorphismEquiv
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u


namespace Prop17

/-- The category of affine schemes over `Y`: schemes equipped with an affine morphism to `Y`
(Def 9, Lec 2). -/
abbrev AffineSchemeOver (Y : Scheme.{u}) :=
  (MorphismProperty.overObj (W := @IsAffineHom) (X := Y)).FullSubcategory

end Prop17

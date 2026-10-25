/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/OpenSubvariety.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Over
import Class.v1.Atlas.AlgebraicGeometryI.code.OpenSubvariety
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u


noncomputable section

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

attribute [instance] IsAlgebraicVariety.isReduced

attribute [instance] IsAlgebraicVariety.isSeparated

attribute [instance] IsAlgebraicVariety.locallyOfFiniteType

attribute [instance] IsAlgebraicVariety.quasiCompact

/-- An open subscheme inherits the structure morphism to S via composition with the
inclusion U ↪ X. -/
instance openSubschemeOver (X : Scheme.{u}) [X.Over S] (U : X.Opens) :
    (↑U : Scheme).Over S :=
  OverClass.ofHom (U.ι ≫ (X ↘ S))

/-- Open subschemes of reduced schemes are reduced. -/
instance isReduced_openSubscheme (X : Scheme.{u}) [IsReduced X] (U : X.Opens) :
    IsReduced (↑U : Scheme) :=
  inferInstance

end AlgebraicGeometry
end

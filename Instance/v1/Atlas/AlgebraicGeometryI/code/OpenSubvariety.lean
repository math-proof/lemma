/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/OpenSubvariety.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Over
public import Class.v1.Atlas.AlgebraicGeometryI.code.OpenSubvariety

@[expose] public section

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

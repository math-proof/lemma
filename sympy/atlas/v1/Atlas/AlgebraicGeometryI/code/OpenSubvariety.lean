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

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- A scheme X is an algebraic variety over a locally Noetherian base S if it is
reduced, separated, of locally finite type and quasi-compact over S. -/
class IsAlgebraicVariety (X : Scheme.{u}) [X.Over S] [IsLocallyNoetherian S] : Prop where
  isReduced : IsReduced X
  isSeparated : X.IsSeparated
  locallyOfFiniteType : LocallyOfFiniteType (X ↘ S)
  quasiCompact : QuasiCompact (X ↘ S)

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

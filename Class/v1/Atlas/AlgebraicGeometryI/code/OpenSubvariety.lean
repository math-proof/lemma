module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/OpenSubvariety.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Over
public section

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

end AlgebraicGeometry
end

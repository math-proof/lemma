/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothPointVariety.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
set_option maxHeartbeats 400000


noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

section SmoothPointDefinition

/-- A locally Noetherian scheme `X` is **smooth at a point `x`** if the local
ring `O_{X,x}` is a regular local ring. -/
def Scheme.IsSmoothAtPoint (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) : Prop :=
  IsRegularLocalRing (X.presheaf.stalk x)

/-- `X` is **singular at `x`** if it is not smooth at `x`. -/
def Scheme.IsSingularAtPoint (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) : Prop :=
  ¬ Scheme.IsSmoothAtPoint X x

/-- `X` is **smooth** if it is smooth at every point. -/
def Scheme.IsSmooth (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  ∀ x : X, Scheme.IsSmoothAtPoint X x

end SmoothPointDefinition
end

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphismDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Def.v1.Atlas.AlgebraicGeometryI.code.GraphMorphismDef
set_option maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u


noncomputable section

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}}

variable (f : X ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S) (w : sX = f ≫ sY)

/-- First projection of the graph morphism is the identity on `X`. -/
@[simp]
lemma graphMorphism_fst :
    graphMorphism f sX sY w ≫ pullback.fst sX sY = 𝟙 X :=
  pullback.lift_fst _ _ _

end AlgebraicGeometry
end

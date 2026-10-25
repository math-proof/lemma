/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphismDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
set_option maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u


noncomputable section

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}}

/-- Graph morphism `Γ_f : X → X ×_S Y` of a morphism `f : X → Y` over `S`,
defined by `(𝟙 X, f)` via the pullback universal property (Def 18, Lec 7). -/
def graphMorphism (f : X ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S) (w : sX = f ≫ sY) :
    X ⟶ pullback sX sY :=
  pullback.lift (𝟙 X) f (by rw [Category.id_comp, w])

end AlgebraicGeometry
end

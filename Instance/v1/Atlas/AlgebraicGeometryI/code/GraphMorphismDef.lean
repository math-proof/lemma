/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphismDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Theorem.v1.Atlas.AlgebraicGeometryI.code.GraphMorphismDef
set_option maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u


noncomputable section

namespace AlgebraicGeometry

variable {S X Y : Scheme.{u}}

variable (f : X ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S) (w : sX = f ≫ sY)

/-- The graph morphism is a split monomorphism, with `pullback.fst` as retraction. -/
instance graphMorphism_isSplitMono :
    IsSplitMono (graphMorphism f sX sY w) :=
  ⟨⟨⟨pullback.fst sX sY, graphMorphism_fst f sX sY w⟩⟩⟩

/-- As a split mono, the graph morphism is in particular a monomorphism. -/
instance graphMorphism_mono :
    Mono (graphMorphism f sX sY w) :=
  IsSplitMono.mono _

/-- If the target `Y → S` is separated, the graph morphism is a closed immersion. -/
instance graphMorphism_isClosedImmersion [IsSeparated sY] :
    IsClosedImmersion (graphMorphism f sX sY w) := by
  subst w
  unfold graphMorphism
  convert (inferInstance : IsClosedImmersion (pullback.lift (𝟙 _) f (Category.id_comp (f ≫ sY))))

end AlgebraicGeometry
end

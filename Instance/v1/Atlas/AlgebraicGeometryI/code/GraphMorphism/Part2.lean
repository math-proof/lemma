/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.AlgebraicGeometryI.code.GraphMorphism
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u


namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The graph morphism is always an immersion. -/
instance isImmersion_graphMor : IsImmersion (graphMor f) :=
  MorphismProperty.of_isPullback (isPullback_graphMor f) inferInstance

/-- If `Y` is separated, the graph morphism is a closed immersion. -/
instance isClosedImmersion_graphMor [Y.IsSeparated] :
    IsClosedImmersion (graphMor f) :=
  MorphismProperty.of_isPullback (isPullback_graphMor f) inferInstance

end AlgebraicGeometry.Scheme

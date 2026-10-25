/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GraphMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.GraphMorphism
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u


namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The graph morphism is a split monomorphism, with `prod.fst` as retraction. -/
noncomputable instance graphMor_splitMono :
    SplitMono (graphMor f) where
  retraction := prod.fst
  id := by simp [graphMor, prod.lift_fst]

end AlgebraicGeometry.Scheme

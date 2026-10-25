/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/K0GeneratorsOverlay.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.K0GeneratorsOverlay


namespace K0Gen

/-- The class `[F] ∈ K^0(Coh X)` of a coherent sheaf `F`. -/
def K0Coh.classOf (X : SmoothCurveK0Data) (F : X.CohSheaf) : K0Coh X :=
  QuotientAddGroup.mk' (sesRelations X) (FreeAbelianGroup.of F)

/-- The map `(r, d) ↦ r·[O_X] + d·[O_x]` from `ℤ × ℤ` into `K^0(Coh X)`. -/
def rankDegToK0 (X : SmoothCurveK0Data) : ℤ × ℤ →+ K0Coh X where
  toFun := fun ⟨r, d⟩ => r • K0Coh.classOf X X.O_X + d • K0Coh.classOf X X.O_x
  map_zero' := by simp
  map_add' := by intro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩; simp only [add_smul]; ac_rfl

end K0Gen

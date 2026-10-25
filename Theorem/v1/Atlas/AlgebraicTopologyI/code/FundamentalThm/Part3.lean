/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part3


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- The lift `lift f P Q` is compatible with the augmentations: composing it with `Q.π`
recovers `P.π` followed by the chain map induced by `f`. -/
@[reassoc (attr := simp)]
theorem lift_commutes {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
  ext
  simp [lift, liftFZero, liftFOne]

end Resolution
end FundamentalThm
end

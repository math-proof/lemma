/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part2


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- Commutativity of the lifted square in degree 1 ↔ 0: `liftFOne` and `liftFZero` form a
commuting square against the differentials. -/
@[simp]
theorem liftFOne_zero_comm {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    liftFOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftFZero f P Q :=
  Q.exact₀.liftFromProjective_comp _ _

end Resolution
end FundamentalThm
end

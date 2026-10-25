/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafDefinitions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.SheafDefinitions
set_option linter.unusedVariables false


namespace SheafDefinitions

open CategoryTheory TopologicalSpace

/-- Pushforward of a presheaf along a covariant functor `u : J ⥤ K`: precompose
with `u.op` to obtain a presheaf on `J` from one on `K`. -/
def pushforwardPresheaf {J K : Type*} [Category J] [Category K]
    {C : Type*} [Category C] (u : J ⥤ K) (F : Presheaf K C) : Presheaf J C :=
  u.op ⋙ F

end SheafDefinitions

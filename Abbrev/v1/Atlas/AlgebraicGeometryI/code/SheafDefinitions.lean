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
set_option linter.unusedVariables false


namespace SheafDefinitions

open CategoryTheory TopologicalSpace

/-- A presheaf on a category `J` with values in `C` is a contravariant functor
`Jᵒᵖ ⥤ C`. -/
abbrev Presheaf (J : Type*) [Category J] (C : Type*) [Category C] := Jᵒᵖ ⥤ C

end SheafDefinitions

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafDefinitions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
@[expose] public section

set_option linter.unusedVariables false


namespace SheafDefinitions

open CategoryTheory TopologicalSpace

/-- A presheaf on a category `J` with values in `C` is a contravariant functor
`Jᵒᵖ ⥤ C`. -/
abbrev Presheaf (J : Type*) [Category J] (C : Type*) [Category C] := Jᵒᵖ ⥤ C

end SheafDefinitions

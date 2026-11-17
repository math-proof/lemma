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
public import Def.v1.Atlas.AlgebraicGeometryI.code.SheafDefinitions

@[expose] public section

set_option linter.unusedVariables false


namespace SheafDefinitions

open CategoryTheory TopologicalSpace

/-- The category of presheaves with values in an abelian category is abelian. -/
noncomputable instance presheafAbelian (C : Type*) [Category C] [Abelian C]
    (J : Type*) [Category J] : Abelian (J ⥤ C) := inferInstance

end SheafDefinitions

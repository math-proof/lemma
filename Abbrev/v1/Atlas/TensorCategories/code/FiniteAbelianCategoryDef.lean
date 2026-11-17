/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteAbelianCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Class.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
@[expose] public section

set_option maxHeartbeats 800000

open CategoryTheory

universe v u


namespace CategoryTheory

/-- Short alias for `Definition_1_18_1_FiniteCategory`. -/
abbrev Definition_1_18_1 := @Definition_1_18_1_FiniteCategory

/-- Short alias for `IsFiniteAbelianCategory` (the intrinsic axioms of Definition 1.18.2
in EGNO). -/
abbrev Definition_1_18_2 := @IsFiniteAbelianCategory

end CategoryTheory

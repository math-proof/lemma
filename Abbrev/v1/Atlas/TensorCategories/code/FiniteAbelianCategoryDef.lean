/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteAbelianCategoryDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Noetherian
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Class.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
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

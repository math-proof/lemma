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
set_option maxHeartbeats 800000

open CategoryTheory

universe v u


namespace CategoryTheory

/-- Definition 1.18.1 (EGNO), explicit form: a `k`-linear abelian category `C` is a
finite category if it is equivalent to the category of finite-dimensional modules over
some finite-dimensional `k`-algebra `A`. -/
def Definition_1_18_1_FiniteCategory
    (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Abelian C] [Linear k C] : Prop :=
  ∃ (A : Type u) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A),
    Nonempty (C ≌ FGModuleCat.{v} A)

end CategoryTheory

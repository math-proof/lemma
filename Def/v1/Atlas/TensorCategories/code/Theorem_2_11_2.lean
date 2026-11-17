/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Theorem_2_11_2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Equivalence
public import Structure.v1.Atlas.TensorCategories.code.Theorem_2_11_2

@[expose] public section

set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂


namespace CategoryTheory

open Category MonoidalCategory

/-- Type of right `A`-modules in `C`, used as the carrier of the category
`Mod_C(A)`. -/
def ModC₂ {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    (A : AlgObj₂ C) :=
  RModObj₂ A

end CategoryTheory

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebraRep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Abbrev.v1.Atlas.TensorCategories.code.HopfAlgebraRep
open CategoryTheory Coalgebra Bialgebra
open scoped TensorProduct

public section

universe u


section RepBialgebra

variable (H : Type u) [Ring H]

example : Preadditive (RepBialgebra H) := inferInstance

end RepBialgebra

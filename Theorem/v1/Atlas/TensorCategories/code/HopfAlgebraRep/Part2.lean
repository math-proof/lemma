module
public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Def.v1.Atlas.TensorCategories.code.HopfAlgebraRep
open CategoryTheory Coalgebra Bialgebra
open scoped TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HopfAlgebraRep.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u


section HopfAlgebraRepCategory

variable (k : Type u) [CommRing k] (H : Type u) [Ring H] [HopfAlgebra k H]

example : Category (RepBialgebra H) := inferInstance

example [HopfAlgebraEGNO k H] : Category (RepBialgebra H) := inferInstance

end HopfAlgebraRepCategory

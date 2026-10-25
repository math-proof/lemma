/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_6_4.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Monoidal.End
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Equivalence
import Mathlib.RingTheory.Finiteness.Basic
import Instance.v1.Atlas.TensorCategories.code.Proposition_1_6_4
set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory


attribute [local instance] endofunctorMonoidalCategory

universe u v


namespace Prop164

/-- The enveloping algebra `A ⊗_k Aᵒᵖ`, whose modules are precisely `A`-bimodules. -/
abbrev EnvelopingAlgebra (k : Type*) [CommRing k] (A : Type*) [Ring A] [Algebra k A] :=
  TensorProduct k A (MulOpposite A)

end Prop164

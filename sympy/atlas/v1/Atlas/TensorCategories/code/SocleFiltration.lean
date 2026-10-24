/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SocleFiltration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.Order.Filter.Basic

universe v u

namespace CategoryTheory

open CategoryTheory

/-- The Loewy length of an object `X` in an abelian category: the length of the shortest
filtration of `X` by semisimple subquotients, declared opaque here as an abstract handle. -/
opaque loewyLength {C : Type u} [Category.{v} C] [Abelian C] (X : C) : ℕ

/-- An object `X` lies in the `i`-th coradical layer of the socle/Loewy filtration when its
Loewy length is at most `i + 1`. -/
def IsInCoradicalLayer {C : Type u} [Category.{v} C] [Abelian C] (i : ℕ) (X : C) : Prop :=
  loewyLength X ≤ i + 1

end CategoryTheory

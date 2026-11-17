/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SnakeLemma.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace SnakeLemma

section AbelianCategory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The connecting homomorphism produced by the snake lemma, mapping the third
object of the top row to the first object of the bottom row. -/
def connectingHomomorphism (S : ShortComplex.SnakeInput C) :
    S.L₀.X₃ ⟶ S.L₃.X₁ :=
  S.δ

end AbelianCategory
end SnakeLemma
end

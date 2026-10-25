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
import Def.v1.Atlas.TensorCategories.code.FiniteAbelianCategoryDef
set_option maxHeartbeats 800000

open CategoryTheory

universe v u


namespace CategoryTheory

/-- Intrinsic axiomatic version of "finite abelian category" over a field `k`: hom-spaces
are finite-dimensional, every object is artinian and noetherian, there are enough
projectives, and there are finitely many isomorphism classes of simple objects. -/
class IsFiniteAbelianCategory
    (k : Type*) [Field k] (A : Type*) [Category A] [Abelian A] [Linear k A] : Prop where
  finiteDimHom : ∀ (X Y : A), Module.Finite k (X ⟶ Y)
  artinian : ∀ (X : A), IsArtinianObject X
  noetherian : ∀ (X : A), IsNoetherianObject X
  enoughProj : EnoughProjectives A
  finitelyManySimples : ∃ (n : ℕ) (S : Fin n → A),
    (∀ i, Simple (S i)) ∧ (∀ (X : A), Simple X → ∃ i, Nonempty (X ≅ S i))

end CategoryTheory

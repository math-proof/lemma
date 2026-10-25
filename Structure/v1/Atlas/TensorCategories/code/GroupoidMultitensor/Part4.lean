/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Pi
import Def.v1.Atlas.TensorCategories.code.GroupoidMultitensor.Part4
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


namespace GroupoidMultitensor

attribute [instance] FiniteGroupoidData.finObj FiniteGroupoidData.finMor

attribute [instance] FiniteGroupoidData.decEqObj FiniteGroupoidData.decEqMor

attribute [instance] GroupoidGradedVecData.instAddCommMonoid GroupoidGradedVecData.instModule

attribute [instance] MatrixVecData.instAddCommMonoid MatrixVecData.instModule

/-- Monoidal structure on `MatrixVecData k n` using matrix multiplication of components. -/
structure ProductMatrixGroupVecData (k : Type w) [Field k]
    {m : ℕ}
    (n : Fin m → ℕ)
    (G : (i : Fin m) → Type w)
    [∀ i, Group (G i)]
    [∀ i, Fintype (G i)]
    [∀ i, DecidableEq (G i)] where
  component : (i : Fin m) → Fin (n i) → Fin (n i) → G i → Type w
  [instAddCommMonoid : ∀ i j₁ j₂ g, AddCommMonoid (component i j₁ j₂ g)]
  [instModule : ∀ i j₁ j₂ g, Module k (component i j₁ j₂ g)]

end GroupoidMultitensor

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Algebra.Pi
public import Def.v1.Atlas.TensorCategories.code.GroupoidMultitensor.Part4
public section

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

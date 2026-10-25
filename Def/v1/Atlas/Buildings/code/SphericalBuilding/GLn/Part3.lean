/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Order.RelClasses
import Mathlib.Data.Matrix.Basic
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.GLn.Part3


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)

/-- A Coxeter matrix is of type $A_{n-1}$ when its diagonal entries are $1$, off-diagonal
entries lie in $\{2,3\}$, and it is symmetric. -/
def TypeA (M : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ) : Prop :=
  (∀ i, M i i = 1) ∧
  (∀ i j, i ≠ j → (M i j = 2 ∨ M i j = 3)) ∧
  (∀ i j, M i j = M j i)

/-- The standard Coxeter matrix of type $A_{n-1}$: ones on the diagonal, threes on adjacent
positions, twos elsewhere. -/
def coxeterMatrixA : Matrix (Fin (n - 1)) (Fin (n - 1)) ℕ := fun i j =>
  if i = j then 1
  else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 3
  else 2

end GLnBuilding

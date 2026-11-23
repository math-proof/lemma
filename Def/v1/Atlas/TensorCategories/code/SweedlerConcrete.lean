/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete

@[expose] public section

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- Structure constants of `SweedlerH4 k` in the basis `e₀ = 1, e₁ = g, e₂ = x, e₃ = gx`: for
each pair `(i, j)`, gives the coefficient of `e_m` in `e_i · e_j`. -/
noncomputable def basisMul (i j : Fin 4) : Fin 4 → k := fun m =>
  match i, j, m with
  | 0, j, m => if j = m then 1 else 0
  | i, 0, m => if i = m then 1 else 0
  | 1, 1, 0 => 1
  | 1, 2, 3 => 1
  | 1, 3, 2 => 1
  | 2, 1, 3 => -1
  | 3, 1, 2 => -1
  | _, _, _ => 0

end SweedlerH4

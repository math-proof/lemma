/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete
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

module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Def.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- `SweedlerH4 k` has `k`-dimension exactly 4, matching its basis `(1, g, x, gx)`. -/
lemma finrank_eq : Module.finrank k (SweedlerH4 k) = 4 := by
  rw [LinearEquiv.finrank_eq toFunEquiv, Module.finrank_fin_fun]

end SweedlerH4

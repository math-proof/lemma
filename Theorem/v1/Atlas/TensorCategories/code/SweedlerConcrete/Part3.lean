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
import Def.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part2
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- `SweedlerH4 k` has `k`-dimension exactly 4, matching its basis `(1, g, x, gx)`. -/
lemma finrank_eq : Module.finrank k (SweedlerH4 k) = 4 := by
  rw [LinearEquiv.finrank_eq toFunEquiv, Module.finrank_fin_fun]

end SweedlerH4

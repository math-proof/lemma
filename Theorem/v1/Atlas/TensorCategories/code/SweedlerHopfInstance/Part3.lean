/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerHopfInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.SweedlerConcrete
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
import Def.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part2
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- The counit evaluates on basis vectors according to the tuple `![1, 1, 0, 0]`. -/
@[simp] lemma counitLM_e (i : Fin 4) :
    counitLM (e i : SweedlerH4 k) = ![1, 1, 0, 0] i := by simp [counitLM]

/-- Counit value on `e 0`: `ε(1) = 1`. -/
@[simp] lemma counitLM_e0 : counitLM (e 0 : SweedlerH4 k) = 1 := by simp [counitLM]

/-- Counit value on `e 1 = g`: `ε(g) = 1`. -/
@[simp] lemma counitLM_e1 : counitLM (e 1 : SweedlerH4 k) = 1 := by simp [counitLM]

/-- Counit value on `e 2 = x`: `ε(x) = 0`. -/
@[simp] lemma counitLM_e2 : counitLM (e 2 : SweedlerH4 k) = 0 := by simp [counitLM]

/-- Counit value on `e 3 = gx`: `ε(gx) = 0`. -/
@[simp] lemma counitLM_e3 : counitLM (e 3 : SweedlerH4 k) = 0 := by simp [counitLM]

/-- Counit preserves the unit: `ε(1) = 1`. -/
@[simp] lemma counitLM_one : counitLM (1 : SweedlerH4 k) = 1 := by
  rw [← e_zero_eq_one]; exact counitLM_e0

end SweedlerH4

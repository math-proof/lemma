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
import Def.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part3
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- Comultiplication value on `e 0 = 1`: `Δ(1) = 1 ⊗ 1`. -/
@[simp] lemma comulLM_e0 : comulLM (e 0 : SweedlerH4 k) = e 0 ⊗ₜ e 0 := by simp [comulLM]

/-- Comultiplication value on `e 1 = g`: `Δ(g) = g ⊗ g`, exhibiting `g` as grouplike. -/
@[simp] lemma comulLM_e1 : comulLM (e 1 : SweedlerH4 k) = e 1 ⊗ₜ e 1 := by simp [comulLM]

/-- Comultiplication value on `e 2 = x`: `Δ(x) = x ⊗ g + 1 ⊗ x`, exhibiting `x` as
`(g, 1)`-skew-primitive. -/
@[simp] lemma comulLM_e2 :
    comulLM (e 2 : SweedlerH4 k) = e 2 ⊗ₜ e 1 + e 0 ⊗ₜ e 2 := by simp [comulLM]

/-- Comultiplication value on `e 3 = gx`: `Δ(gx) = gx ⊗ 1 + g ⊗ gx`. -/
@[simp] lemma comulLM_e3 :
    comulLM (e 3 : SweedlerH4 k) = e 3 ⊗ₜ e 0 + e 1 ⊗ₜ e 3 := by simp [comulLM]

/-- Comultiplication preserves the unit: `Δ(1) = 1 ⊗ 1`. -/
@[simp] lemma comulLM_one : comulLM (1 : SweedlerH4 k) = e 0 ⊗ₜ e 0 := by
  rw [← e_zero_eq_one]; exact comulLM_e0

end SweedlerH4

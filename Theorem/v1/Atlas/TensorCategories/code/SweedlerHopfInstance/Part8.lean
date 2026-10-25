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
import Instance.v1.Atlas.TensorCategories.code.SweedlerHopfInstance.Part3
set_option linter.unusedSimpArgs false

open Coalgebra HopfAlgebra
open scoped TensorProduct

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- The generator `g` is grouplike: `Δ(g) = g ⊗ g`. -/
lemma comul_gen_g :
    (Coalgebra.comul (R := k)) (gen_g : SweedlerH4 k) =
      (gen_g : SweedlerH4 k) ⊗ₜ gen_g := by
  show comulLM (e 1 : SweedlerH4 k) = e 1 ⊗ₜ e 1; simp

/-- The generator `x` is `(g, 1)`-skew-primitive: `Δ(x) = x ⊗ g + 1 ⊗ x`. -/
lemma comul_gen_x :
    (Coalgebra.comul (R := k)) (gen_x : SweedlerH4 k) =
      (gen_x : SweedlerH4 k) ⊗ₜ gen_g + (1 : SweedlerH4 k) ⊗ₜ gen_x := by
  show comulLM (e 2 : SweedlerH4 k) =
    (e 2 : SweedlerH4 k) ⊗ₜ e 1 + (1 : SweedlerH4 k) ⊗ₜ e 2
  rw [← e_zero_eq_one]; simp

/-- Counit value `ε(g) = 1`. -/
lemma counit_gen_g :
    (Coalgebra.counit (R := k)) (gen_g : SweedlerH4 k) = (1 : k) := by
  show counitLM (e 1 : SweedlerH4 k) = 1; simp

/-- Counit value `ε(x) = 0`. -/
lemma counit_gen_x :
    (Coalgebra.counit (R := k)) (gen_x : SweedlerH4 k) = (0 : k) := by
  show counitLM (e 2 : SweedlerH4 k) = 0; simp

/-- Antipode value `S(g) = g`. -/
lemma antipode_gen_g :
    (HopfAlgebra.antipode k) (gen_g : SweedlerH4 k) = gen_g := by
  show antipodeLM (e 1 : SweedlerH4 k) = e 1; simp

/-- Antipode value `S(x) = g · x = gx`. -/
lemma antipode_gen_x :
    (HopfAlgebra.antipode k) (gen_x : SweedlerH4 k) =
      (gen_g : SweedlerH4 k) * gen_x := by
  show antipodeLM (e 2 : SweedlerH4 k) = (e 1 : SweedlerH4 k) * e 2
  rw [show (e 1 : SweedlerH4 k) * e 2 = e 3 from e1_mul_e2]; simp

end SweedlerH4

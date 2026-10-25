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
import Instance.v1.Atlas.TensorCategories.code.SweedlerConcrete
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- All coefficients of `0 : SweedlerH4 k` are zero. -/
@[simp] lemma coeff_zero' (i : Fin 4) : (0 : SweedlerH4 k).coeff i = 0 := rfl

/-- Componentwise formula for addition coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_add (a b : SweedlerH4 k) (i : Fin 4) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl

/-- Componentwise formula for negation coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_neg (a : SweedlerH4 k) (i : Fin 4) :
    (-a).coeff i = -a.coeff i := rfl

/-- Componentwise formula for subtraction coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_sub (a b : SweedlerH4 k) (i : Fin 4) :
    (a - b).coeff i = a.coeff i - b.coeff i := rfl

/-- Componentwise formula for scalar multiplication coefficients in `SweedlerH4 k`. -/
@[simp] lemma coeff_smul (r : k) (a : SweedlerH4 k) (i : Fin 4) :
    (r • a).coeff i = r * a.coeff i := rfl

end SweedlerH4

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
public import Instance.v1.Atlas.TensorCategories.code.SweedlerConcrete

public section

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

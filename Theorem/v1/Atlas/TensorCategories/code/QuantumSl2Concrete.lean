/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean -/

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
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuantumSl2
public import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Concrete

public section

variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- Coefficients of the zero element vanish. -/
@[simp] lemma coeff_zero' (i : Fin n × Fin n × Fin n) :
    (0 : SmallQuantumSl2 n k).coeff i = 0 := rfl

/-- Coefficients of a sum are sums of coefficients. -/
@[simp] lemma coeff_add (a b : SmallQuantumSl2 n k) (i : Fin n × Fin n × Fin n) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl

/-- Coefficients of a negation are negations of coefficients. -/
@[simp] lemma coeff_neg (a : SmallQuantumSl2 n k) (i : Fin n × Fin n × Fin n) :
    (-a).coeff i = -a.coeff i := rfl

/-- Coefficients of a difference are differences of coefficients. -/
@[simp] lemma coeff_sub (a b : SmallQuantumSl2 n k) (i : Fin n × Fin n × Fin n) :
    (a - b).coeff i = a.coeff i - b.coeff i := rfl

/-- Coefficients of a scalar multiple. -/
@[simp] lemma coeff_smul (r : k) (a : SmallQuantumSl2 n k) (i : Fin n × Fin n × Fin n) :
    (r • a).coeff i = r * a.coeff i := rfl

end SmallQuantumSl2

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean -/

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
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.RingQuot
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
import Lemma.Category.Atlas.v1.TensorCategories.code.QuantumSl2
import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
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

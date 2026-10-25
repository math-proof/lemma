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
import Instance.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part2
variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- Linear equivalence between `SmallQuantumSl2 n k` and the coordinate space
`Fin n × Fin n × Fin n → k`. -/
noncomputable def toFunEquiv :
    SmallQuantumSl2 n k ≃ₗ[k] (Fin n × Fin n × Fin n → k) where
  toFun a := a.coeff
  invFun f := ⟨f⟩
  map_add' a b := rfl
  map_smul' r a := by ext i; simp [Pi.smul_apply, smul_eq_mul]
  left_inv a := rfl
  right_inv f := rfl

end SmallQuantumSl2

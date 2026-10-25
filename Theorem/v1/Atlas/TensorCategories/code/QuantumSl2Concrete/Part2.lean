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
import Def.v1.Atlas.TensorCategories.code.QuantumSl2Concrete.Part2
variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- Coefficient formula for `basisVec`. -/
@[simp] lemma coeff_basisVec (i j : Fin n × Fin n × Fin n) :
    (basisVec i : SmallQuantumSl2 n k).coeff j = if i = j then 1 else 0 := rfl


end SmallQuantumSl2

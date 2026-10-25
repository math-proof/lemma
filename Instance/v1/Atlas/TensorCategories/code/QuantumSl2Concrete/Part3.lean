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
import Def.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- `SmallQuantumSl2 n k` is a finite `k`-module. -/
noncomputable instance : Module.Finite k (SmallQuantumSl2 n k) :=
  Module.Finite.equiv toFunEquiv.symm

/-- `SmallQuantumSl2 n k` is finite-dimensional over `k`. -/
instance finiteDimensional : FiniteDimensional k (SmallQuantumSl2 n k) := inferInstance

end SmallQuantumSl2

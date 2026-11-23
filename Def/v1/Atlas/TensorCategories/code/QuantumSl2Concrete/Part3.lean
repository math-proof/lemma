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
public import Abbrev.v1.Atlas.TensorCategories.code.QuantumSl2Concrete

@[expose] public section

variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

variable (n : ℕ) (k : Type*) [Field k] (q : k)

namespace SmallQuantumSl2Alg

/-- The generator `K` of the small quantum group `u_q(sl_2)`. -/
noncomputable def K : SmallQuantumSl2Alg n k q := π n k q (FreeAlgebra.ι k 0)

/-- The generator `E` of the small quantum group `u_q(sl_2)`. -/
noncomputable def E : SmallQuantumSl2Alg n k q := π n k q (FreeAlgebra.ι k 1)

/-- The generator `F` of the small quantum group `u_q(sl_2)`. -/
noncomputable def F : SmallQuantumSl2Alg n k q := π n k q (FreeAlgebra.ι k 2)

/-- The inverse `K⁻¹` of `K`, realized as `K^{n-1}` (using `K^n = 1`). -/
noncomputable def Kinv : SmallQuantumSl2Alg n k q := K n k q ^ (n - 1)

end SmallQuantumSl2Alg
end SmallQuantumSl2

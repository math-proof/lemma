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
import Abbrev.v1.Atlas.TensorCategories.code.QuantumSl2Concrete
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

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyP1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Int.Interval
set_option maxHeartbeats 400000


namespace CohomologyP1

variable (k : Type) [Field k]


/-- The submodule of finitely supported integer-indexed `k`-functions supported on `ℤ_{≥0}`,
modelling the global sections of `O(n)` on one affine chart of `P^1`. -/
noncomputable def NonNeg : Submodule k (ℤ →₀ k) :=
  Finsupp.supported k k (Set.Ici 0)

/-- The submodule of finitely supported integer-indexed `k`-functions supported on `(-∞, n]`,
modelling the other affine chart contribution to `O(n)` on `P^1`. -/
noncomputable def AtMost (n : ℤ) : Submodule k (ℤ →₀ k) :=
  Finsupp.supported k k (Set.Iic n)

/-- The Čech `H^0(P^1, O(n))`: the intersection of the two chart submodules `NonNeg` and
`AtMost n`. -/
noncomputable def CechH0 (n : ℤ) : Submodule k (ℤ →₀ k) :=
  NonNeg k ⊓ AtMost k n


end CohomologyP1

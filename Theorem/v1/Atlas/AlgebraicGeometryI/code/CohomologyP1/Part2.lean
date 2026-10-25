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
import Def.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
set_option maxHeartbeats 400000


namespace CohomologyP1

variable (k : Type) [Field k]


/-- For `n < 0`, `H^1(P^1, O(n))` has dimension `(-n - 1).toNat`. -/
theorem finrank_H1_neg (n : ℤ) (_ : n < 0) :
    Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) = (-n - 1).toNat := by
  rw [(H1_equiv_supported_complement k n).finrank_eq, finrank_supported_eq_card]
  rw [← Set.toFinset_card, Set.toFinset_Ioo, Int.card_Ioo]
  ring_nf

end CohomologyP1

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
import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1
set_option maxHeartbeats 400000


namespace CohomologyP1

variable (k : Type) [Field k]


/-- Linear equivalence between the cokernel of the Čech differential and the submodule supported
on the missing integer range `Set.Ioo n 0`. -/
noncomputable def H1_equiv_supported_complement (n : ℤ) :
    ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) ≃ₗ[k]
      ↥(Finsupp.supported k k (Set.Ioo n 0)) := by
  rw [sum_eq_supported]
  have hc : IsCompl (Finsupp.supported k k (Set.Ici (0 : ℤ) ∪ Set.Iic n))
      (Finsupp.supported k k (Set.Ioo n 0)) := by
    rw [← complement_union]
    exact ⟨Finsupp.disjoint_supported_supported isCompl_compl.disjoint,
           Finsupp.codisjoint_supported_supported isCompl_compl.codisjoint⟩
  exact Submodule.quotientEquivOfIsCompl _ _ hc

end CohomologyP1

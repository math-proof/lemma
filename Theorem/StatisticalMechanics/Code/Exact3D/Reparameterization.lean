/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
import Structure.StatisticalMechanics.Code.Exact3D.Reparameterization


namespace StatMech

namespace Exact3D

namespace LeftCriticalReparam

theorem id {ι : Type*} (M : CriticalModel ι) :
    LeftCriticalReparam M M id where
  tendsto_left := Filter.tendsto_id
  log_distance_ratio := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards
      [Ioo_mem_nhdsLT (show M.betaC - 1 < M.betaC by linarith)] with β hβ
    have hdiff : M.betaC - β ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor <;> linarith [hβ.1, hβ.2]
    have hlog_ne : Real.log (M.betaC - β) ≠ 0 :=
      (Real.log_neg hdiff.1 hdiff.2).ne
    rw [show _root_.id β = β by rfl]
    field_simp [hlog_ne]


end LeftCriticalReparam
end Exact3D
end StatMech

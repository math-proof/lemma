/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part12
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailCone.Part3


namespace StatMech

namespace Exact3D

namespace FinitePlusTailHyperbolicSplitting

variable {n : ℕ} {α : Type*}


theorem cone_step
    (H : FinitePlusTailHyperbolicSplitting n α)
    {η : ℝ} (hη : 0 ≤ η) {x : State n α}
    (hx : H.cone η x) :
    H.cone η (H.step x) := by
  change
    FinitePlusTailState.ThermalStableCone η
      (H.thermal * x.1) (H.stable.map x.2)
  change FinitePlusTailState.ThermalStableCone η x.1 x.2 at hx
  exact
    H.stable.map_mem_thermalStableCone_of_c_le_abs_thermal
      H.stable_origin hη H.stable_dominated hx


theorem cone_iterate
    (H : FinitePlusTailHyperbolicSplitting n α)
    {η : ℝ} (hη : 0 ≤ η) {x : State n α}
    (hx : H.cone η x) (k : ℕ) :
    H.cone η (H.iterate k x) := by
  change
    FinitePlusTailState.ThermalStableCone η
      (H.iterate k x).1 (H.iterate k x).2
  change FinitePlusTailState.ThermalStableCone η x.1 x.2 at hx
  rw [H.iterate_fst_eq k x, H.iterate_snd_eq k x]
  exact
    H.stable.iterate_mem_thermalStableCone_of_c_le_abs_thermal
      H.stable_origin hη H.stable_dominated hx k

end FinitePlusTailHyperbolicSplitting
end Exact3D
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
import Def.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part3
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


theorem CriticalSurfacePhaseBoundary.eq_zero
    {surface : ℝ → ℝ} {pc : ℝ}
    (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hphase : CriticalSurfacePhaseBoundary surface pc) :
    surface pc = 0 := by
  have hsign := hphase pc hpc
  have hnotNeg : ¬surface pc < 0 := by
    rw [hsign.1]
    exact lt_irrefl pc
  have hnotPos : ¬0 < surface pc := by
    rw [hsign.2]
    exact lt_irrefl pc
  exact le_antisymm (le_of_not_gt hnotPos) (le_of_not_gt hnotNeg)


end PeriodicPlanar
end FK
end StatMech

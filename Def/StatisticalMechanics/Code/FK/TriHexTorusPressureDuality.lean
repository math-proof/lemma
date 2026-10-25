/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusComparison.Part2
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusPressureDuality
open Finset Set SimpleGraph Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable def triHexTorusPartitionCorrectionLogDensity
    (p q : ℝ) (n : ℕ) : ℝ := by
  let L := n + 3
  letI : Fact (2 < L) := ⟨by simp [L]⟩
  exact Real.log
    (triHexTorusDefectWeightedDualPartitionSum L
        (BeffaraDC.dualParam p q) q /
      triHexTorusDualPartitionSum L (BeffaraDC.dualParam p q) q) /
    (L ^ 2 : ℕ)


end PeriodicPlanar
end FK
end StatMech

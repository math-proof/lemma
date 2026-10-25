/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusPressureDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexTorusComparison.Part2
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusPressureDuality.Part2
open Finset Set SimpleGraph Filter Topology


namespace StatMech

namespace FK

namespace PeriodicPlanar

noncomputable def triHexTorusPressureDualityResidual
    (L : ℕ) [Fact (2 < L)] (p q : ℝ) : ℝ :=
  let pDual := BeffaraDC.dualParam p q
  let m := (triangularTorusGraph L).edgeFinset.card
  let v := Nat.card (TorusSite L)
  (Real.log (triHexTorusPrimalPartitionSum L p q) +
      (m + 1 : ℝ) * Real.log q -
    ((m : ℝ) * Real.log (p / (1 - pDual)) +
      (v : ℝ) * Real.log q +
      Real.log (triHexTorusDualPartitionSum L pDual q))) /
    (L ^ 2 : ℕ)


end PeriodicPlanar
end FK
end StatMech

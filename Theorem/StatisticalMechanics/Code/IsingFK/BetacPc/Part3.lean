/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/BetacPc.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Def.StatisticalMechanics.Code.Ising.Magnetization.Part3
import Def.StatisticalMechanics.Code.IsingFK.BetacPc.Part3
open Real


namespace StatMech

namespace IsingFK

theorem isingBetaC_eq (d : ℕ)
    (hnonneg : ∀ β, 0 ≤ Ising.magnetization d β)
    (hpos_iff : ∀ β, 0 < β →
      (0 < Ising.magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β))
    (hpos : 0 < pToBeta 2 (FK.fkPc d 2)) :
    isingBetaC d = -(1 / 2) * Real.log (1 - FK.fkPc d 2) := by
  unfold isingBetaC
  rw [betaC_eq (Ising.magnetization d) 2 (FK.fkPc d 2) hnonneg hpos_iff hpos, pToBeta_two]

end IsingFK
end StatMech

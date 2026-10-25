/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusSpinSectors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CoeffMatch
import Theorem.StatisticalMechanics.Code.Onsager.Torus
import Def.StatisticalMechanics.Code.Onsager.TorusSpinSectors.Part2


namespace StatMech.Onsager

open StatMech.Ising


theorem ons_X_eq_sum_sectorWeight (L : ℕ) [Fact (2 < L)] (x : ℝ) :
    ons_X (onsTorusGraph L) x = ∑ h : Fin 2 × Fin 2, ons_sectorWeight L x h := by
  rw [ons_X_eq_sum_evenSubgraphs]
  exact (Finset.sum_fiberwise (evenSubgraphs (onsTorusGraph L))
    (ons_evenHomology L) (fun F => x ^ F.card)).symm

end StatMech.Onsager

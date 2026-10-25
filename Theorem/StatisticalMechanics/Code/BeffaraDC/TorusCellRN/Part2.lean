/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellRN.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellFKDuality
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellDefectClassify.Part3
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part2
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torusAmbientFKWeight_duality_signed
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    torusAmbientFKWeight L p q omega *
        q ^ ((onsTorusGraph L).edgeFinset.card + 1) =
      (p / (1 - dualParam p q)) ^ (onsTorusGraph L).edgeFinset.card *
        q ^ Nat.card (ZMod L × ZMod L) *
        torusAmbientFKWeight L (dualParam p q) q
          (torusCellDualAmbientConfig L omega) *
        q ^ torusCellDefect L
          (FK.openSub (onsTorusGraph L) (torusAmbientConfigExtend L omega)) := by
  unfold torusAmbientFKWeight
  rw [torusAmbientConfigExtend_dual]
  exact torusCell_fkWeight_duality_signed L
    (torusAmbientConfigExtend L omega) hp hp1 hq


end StatMech.BeffaraDC

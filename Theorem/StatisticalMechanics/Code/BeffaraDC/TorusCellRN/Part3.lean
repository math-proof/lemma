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
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part3
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torusAmbientDefect_classified (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    torusAmbientDefect L omega = 0 ∨ torusAmbientDefect L omega = 1 ∨
      torusAmbientDefect L omega = 2 := by
  unfold torusAmbientDefect
  exact torusCellDefect_classified_unconditional L _
    (FK.openSub_le (onsTorusGraph L) (torusAmbientConfigExtend L omega))


theorem torusAmbientDefect_add_dual (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    torusAmbientDefect L omega +
      torusAmbientDefect L (torusCellDualAmbientConfig L omega) = 2 := by
  unfold torusAmbientDefect
  rw [torusAmbientConfigExtend_dual]
  exact torusCellDefect_add_dualConfig L (torusAmbientConfigExtend L omega)


end StatMech.BeffaraDC

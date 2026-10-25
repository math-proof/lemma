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
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellRN
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


@[simp] theorem torusAmbientConfigRestrict_extend
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    torusAmbientConfigRestrict L (torusAmbientConfigExtend L omega) = omega := by
  funext e
  simp [torusAmbientConfigRestrict, torusAmbientConfigExtend, e.2]


theorem torusAmbientConfigExtend_dual (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (torusCellDualAmbientConfig L omega) =
      torusCellDualConfig L (torusAmbientConfigExtend L omega) := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset
  · have hp := torusCellPrimalOfDualEdge_mem L he
    have hp' : (((torusCellCrossing L).symm
        (⟨e, he⟩ : TorusAmbientEdge L) : TorusAmbientEdge L) :
        Sym2 (ZMod L × ZMod L)) ∈ (onsTorusGraph L).edgeFinset :=
      ((torusCellCrossing L).symm (⟨e, he⟩ : TorusAmbientEdge L)).2
    rw [torusAmbientConfigExtend, dif_pos he, torusCellDualConfig,
      dif_pos he, torusCellDualAmbientConfig]
    rw [torusCellPrimalOfDualEdge_of_mem L he]
    rw [torusAmbientConfigExtend, dif_pos hp']
  · rw [torusAmbientConfigExtend, dif_neg he, torusCellDualConfig, dif_neg he]


end StatMech.BeffaraDC

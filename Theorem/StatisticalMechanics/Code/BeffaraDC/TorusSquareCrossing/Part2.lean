/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossing.Part2
open SimpleGraph Set
open scoped BigOperators


namespace StatMech.BeffaraDC

open StatMech.Onsager


theorem torusAmbientConfigExtend_swap (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) :
    torusAmbientConfigExtend L (torusAmbientSwapConfig L omega) =
      FK.reCfgIso (torusCoordSwap L) (torusAmbientConfigExtend L omega) := by
  funext e
  by_cases he : e ∈ (onsTorusGraph L).edgeFinset
  · have hse : Sym2.map (torusCoordSwap L) e ∈
        (onsTorusGraph L).edgeFinset :=
      (torusCoordSwap_mem_edgeFinset_iff L e).2 he
    rw [torusAmbientConfigExtend, dif_pos he, FK.fvs_reCfgIso_apply,
      torusAmbientConfigExtend, dif_pos hse]
    unfold torusAmbientSwapConfig
    congr 2
  · have hse : Sym2.map (torusCoordSwap L) e ∉
        (onsTorusGraph L).edgeFinset := by
      intro h
      exact he ((torusCoordSwap_mem_edgeFinset_iff L e).1 h)
    rw [torusAmbientConfigExtend, dif_neg he, FK.fvs_reCfgIso_apply,
      torusAmbientConfigExtend, dif_neg hse]


theorem torusAmbientFKWeight_swap (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (omega : TorusAmbientConfig L) :
    torusAmbientFKWeight L p q (torusAmbientSwapConfig L omega) =
      torusAmbientFKWeight L p q omega := by
  unfold torusAmbientFKWeight
  rw [torusAmbientConfigExtend_swap]
  exact FK.fvs_fkWeight_reCfgIso (onsTorusGraph L) (onsTorusGraph L)
    (torusCoordSwap L) (fun x y => (onsTorusGraph_adj_coordSwap L x y).symm)
    p q (torusAmbientConfigExtend L omega)


theorem torusAmbientProbability_swap (L : ℕ) [Fact (2 < L)]
    (p q : ℝ) (omega : TorusAmbientConfig L) :
    torusAmbientProbability L p q (torusAmbientSwapConfig L omega) =
      torusAmbientProbability L p q omega := by
  unfold torusAmbientProbability
  rw [torusAmbientFKWeight_swap]


end StatMech.BeffaraDC

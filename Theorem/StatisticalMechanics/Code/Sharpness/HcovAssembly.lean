/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HcovAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.DeltaRewriteDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyDischarge
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Def.StatisticalMechanics.Code.Sharpness.HcovAssembly
open Finset BigOperators SimpleGraph
open scoped symmDiff Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


namespace StatMech

namespace Sharpness

namespace HcovAssembly

open StatMech.Sharpness (ofEdgeFun weight currentSum)

open StatMech.Sharpness.FluxEdgeCopy (Copy endsM endsM_not_isDiag sourcePairDisconnSum
  sourcePairDisconnSum_eq_switching_gap)

open StatMech.Sharpness.RandomCurrent (connK switching_disconnect_card)

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (H : SimpleGraph V) [DecidableRel H.Adj]


theorem hca_gap_disconn (m : ↥H.edgeFinset → ℕ) (A : Finset V) {u v : V} (huv : u ≠ v) :
    hca_gap H m A u v
      = (if ¬ connK (endsM H m) univ u v then (1 : ℝ) else 0) * hca_gap H m A u v := by
  classical
  unfold hca_gap
  by_cases hAm : RandomCurrent.sources (endsM H m) univ = A
  · rw [if_pos hAm]
    have hsw := switching_disconnect_card (endsM H m) (univ : Finset (Copy H m))
      (fun i _ => endsM_not_isDiag H m i) A hAm huv
    by_cases hC : connK (endsM H m) univ u v
    · 
      rw [if_neg (not_not.mpr hC)] at hsw
      have hgapR : ((#((univ : Finset (Copy H m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM H m) K = A)) : ℝ)
            - #((univ : Finset (Copy H m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM H m) K = A ∆ {u, v}))) = 0 := by
        have hz : ((#((univ : Finset (Copy H m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM H m) K = A)) : ℤ)
            - #((univ : Finset (Copy H m)).powerset.filter
              (fun K => RandomCurrent.sources (endsM H m) K = A ∆ {u, v}))) = 0 := by omega
        exact_mod_cast hz
      rw [hgapR, if_neg (not_not.mpr hC), zero_mul]
    · rw [if_pos hC, one_mul]
  · rw [if_neg hAm, mul_zero]


end HcovAssembly
end Sharpness
end StatMech

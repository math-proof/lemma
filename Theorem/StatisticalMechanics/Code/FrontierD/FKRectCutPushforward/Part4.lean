/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part4
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

@[simp] theorem fkRectGraphForceOpen_of_mem
    (R : FKRectTorus)
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (eta : FKRectGraphConfiguration R) {e} (he : e ∈ I) :
    fkRectGraphForceOpen R I eta e = true := by
  simp [fkRectGraphForceOpen, he]

@[simp] theorem fkRectGraphForceOpen_of_not_mem
    (R : FKRectTorus)
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (eta : FKRectGraphConfiguration R) {e} (he : e ∉ I) :
    fkRectGraphForceOpen R I eta e = eta e := by
  simp [fkRectGraphForceOpen, he]


theorem fkRectGraphCritical_cFE_pow_mul_forceOpen_preimage_le_event
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (A : Set (FKRectGraphConfiguration R)) :
    FK.cFE (fkRectCriticalP q) q ^ I.card *
        fkRectGraphCriticalEventMass R q
          (fkRectGraphForceOpen R I ⁻¹' A) ≤
      fkRectGraphCriticalEventMass R q A := by
  simpa [fkRectGraphCriticalEventMass, fkRectGraphForceOpen,
    finiteBoolEventMass, finiteBoolForceOpen] using
    finiteBool_c_pow_mul_forceOpen_preimage_le_event
      (fun eta => fkRectGraphCriticalRandomClusterProb R q eta)
      (fun eta => fkRectGraphCriticalRandomClusterProb_nonneg R
        (lt_of_lt_of_le zero_lt_one hq) eta)
      (FK.cFE (fkRectCriticalP q) q) (fkRectCritical_cFE_nonneg hq)
      (fkRectGraphCriticalProb_setOpen_ge R hq) I A


end
end StatMech.FrontierD

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamForcing.Part5
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward
open Finset SimpleGraph

set_option maxHeartbeats 800000


namespace StatMech.FrontierD

noncomputable section

open StatMech

@[simp] theorem fkRectGraphForceClosed_of_mem
    (R : FKRectTorus)
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (eta : FKRectGraphConfiguration R) {e} (he : e ∈ I) :
    fkRectGraphForceClosed R I eta e = false := by
  simp [fkRectGraphForceClosed, he]

@[simp] theorem fkRectGraphForceClosed_of_not_mem
    (R : FKRectTorus)
    {I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet}}
    (eta : FKRectGraphConfiguration R) {e} (he : e ∉ I) :
    fkRectGraphForceClosed R I eta e = eta e := by
  simp [fkRectGraphForceClosed, he]

@[simp] theorem fkRectGraphForceClosed_empty
    (R : FKRectTorus) (eta : FKRectGraphConfiguration R) :
    fkRectGraphForceClosed R ∅ eta = eta := by
  funext e
  simp [fkRectGraphForceClosed]

theorem fkRectGraphForceClosed_insert
    (R : FKRectTorus)
    (I : Finset {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    fkRectGraphForceClosed R (insert e I) eta =
      fkRectGraphForceClosed R I (setClosed e eta) := by
  funext x
  by_cases hx : x = e
  · subst x
    simp [fkRectGraphForceClosed]
  · by_cases hxI : x ∈ I
    · simp [fkRectGraphForceClosed, hx, hxI]
    · simp [fkRectGraphForceClosed, hx, hxI, setClosed_of_ne]


end
end StatMech.FrontierD

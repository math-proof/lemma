/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part8


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

def HexCyclicLaunch.toEndpointTriplet
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).IsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn region)
    (hsuccMem : region (labelMid v du (hexCyclicSucc j)))
    (hpredMem : region (labelMid v du (hexCyclicPred j))) :
    HexEndpointCyclicTriplet region a h0 v du where
  baseLabel := j
  base := ts
  base_valid := by
    refine ⟨⟨hlegal.1, ?_⟩, hstay, L.endsAt⟩
    exact (List.dropLast_sublist _).nodup hlegal.2
  succ_valid := by
    refine ⟨(endpointIsLegalSAW_append_one_iff a h0 ts (-1)).2
      ⟨hlegal, Or.inr rfl⟩, ?_, L.succ_endsAt⟩
    exact (hexCyclic_staysIn_concat_single_iff region a h0 (-1) ts).2
      ⟨hstay, by simpa [L.succ_newMid] using hsuccMem⟩
  pred_valid := by
    refine ⟨(endpointIsLegalSAW_append_one_iff a h0 ts 1).2
      ⟨hlegal, Or.inl rfl⟩, ?_, L.pred_endsAt⟩
    exact (hexCyclic_staysIn_concat_single_iff region a h0 1 ts).2
      ⟨hstay, by simpa [L.pred_newMid] using hpredMem⟩


def HexCyclicLaunch.toEndpointTripletOfCountOne
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    {j : Fin 3} {ts : List ℤ}
    (L : HexCyclicLaunch a h0 v du j ts)
    (hlegal : (ofTurns a h0 ts).EndpointIsLegalSAW)
    (hstay : (ofTurns a h0 ts).StaysIn region)
    (hcount : specialMidCount a h0 v du ts = 1)
    (hsuccMem : region (labelMid v du (hexCyclicSucc j)))
    (hpredMem : region (labelMid v du (hexCyclicPred j))) :
    HexEndpointCyclicTriplet region a h0 v du :=
  L.toEndpointTriplet
    (hexEndpoint_full_legal_of_count_one a h0 v du j ts L hlegal hcount)
    hstay hsuccMem hpredMem


end
end StatMech.Universality

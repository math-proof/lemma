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
import Def.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part9


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

theorem hexEndpoint_kTwo_mem_cyclicTriplet
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (j : Fin 3) (base : List ℤ) (t : ℤ) (hdu : du ≠ 0)
    (hvalid : (ofTurns a h0 (base ++ [t])).EndpointIsLegalSAW ∧
      (ofTurns a h0 (base ++ [t])).StaysIn region ∧
      (ofTurns a h0 (base ++ [t])).EndsAt (labelMid v du j))
    (hcount : specialMidCount a h0 v du (base ++ [t]) = 2)
    (hlast : hexInfra_midAccum a h0 base +
      halfStep (hexInfra_headAccum h0 base) = v)
    (hnew : ¬ PassesThrough a h0 base (labelMid v du j))
    (hall : ∀ l : Fin 3, region (labelMid v du l)) :
    ∃ C : HexEndpointCyclicTriplet region a h0 v du,
      base ++ [t] ∈ C.piece ∧ C.base = base := by
  have happ := (endpointIsLegalSAW_append_one_iff a h0 base t).mp hvalid.1
  obtain ⟨l, _, L⟩ := hexEndpoint_erase_last_launch
    a h0 v du j base t happ.2 hlast hvalid.2.2
  have hbaseEndpoint : (ofTurns a h0 base).EndpointIsLegalSAW := by
    refine ⟨happ.1.1, ?_⟩
    exact (List.dropLast_sublist _).nodup happ.1.2
  have hbaseStay : (ofTurns a h0 base).StaysIn region :=
    (hexCyclic_staysIn_concat_single_iff region a h0 t base).mp hvalid.2.1 |>.1
  have hbaseCount : specialMidCount a h0 v du base = 1 :=
    hexEndpoint_base_count_one_of_extension_count_two
      a h0 v du j base t hdu hvalid.2.2 hnew hcount
  let C := L.toEndpointTripletOfCountOne hbaseEndpoint hbaseStay hbaseCount
    (hall (hexCyclicSucc l)) (hall (hexCyclicPred l))
  have hCbase : C.base = base := rfl
  refine ⟨C, ?_, hCbase⟩
  rcases happ.2 with rfl | rfl
  · change base ++ [1] ∈ {C.base, C.base ++ [-1], C.base ++ [1]}
    rw [hCbase]
    simp
  · change base ++ [-1] ∈ {C.base, C.base ++ [-1], C.base ++ [1]}
    rw [hCbase]
    simp

theorem hexCyclicSucc_ne_pred (j : Fin 3) :
    hexCyclicSucc j ≠ hexCyclicPred j := by
  fin_cases j <;> decide


theorem HexEndpointCyclicTriplet.sum_piece_zero
    {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}
    (hdu : du ≠ 0) (C : HexEndpointCyclicTriplet region a h0 v du) :
    ∑ ts ∈ C.piece, endpointCombinedSummand region a h0 v du ts = 0 := by
  have hbase_succ : C.base ≠ C.base ++ [-1] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hbase_pred : C.base ≠ C.base ++ [1] := by
    intro h
    have := congrArg List.length h
    simp at this
  have hsucc_pred : C.base ++ [-1] ≠ C.base ++ [1] := by
    intro heq
    have hm : labelMid v du (hexCyclicSucc C.baseLabel) =
        labelMid v du (hexCyclicPred C.baseLabel) :=
      C.succ_valid.2.2.symm.trans (heq ▸ C.pred_valid.2.2)
    exact hexCyclicSucc_ne_pred C.baseLabel (labelMid_injective hdu hm)
  rw [show (∑ ts ∈ C.piece,
      endpointCombinedSummand region a h0 v du ts) =
      endpointCombinedSummand region a h0 v du C.base +
        endpointCombinedSummand region a h0 v du (C.base ++ [-1]) +
        endpointCombinedSummand region a h0 v du (C.base ++ [1]) by
    simp [HexEndpointCyclicTriplet.piece, hbase_succ, hbase_pred,
      hsucc_pred]
    ring]
  rw [endpointCombinedSummand_at_label hdu C.baseLabel C.base_valid.2.2,
    endpointCombinedSummand_at_label hdu (hexCyclicSucc C.baseLabel)
      C.succ_valid.2.2,
    endpointCombinedSummand_at_label hdu (hexCyclicPred C.baseLabel)
      C.pred_valid.2.2]
  exact C.contribution_zero


end
end StatMech.Universality

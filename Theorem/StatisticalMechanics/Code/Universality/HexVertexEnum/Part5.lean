/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part3


namespace StatMech.Universality

open Complex

open HexWalk


namespace HexVertexEnumeration

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem vertexSum_toVertexWalkData (E : HexVertexEnumeration region a h0 v du) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi
      = (toVertexWalkData E).vertexSum := by
  rw [E.reindex]
  unfold toVertexWalkData VertexWalkData.vertexSum
  simp only
  congr 1
  · 
    apply Finset.sum_congr rfl
    intro P hP
    rw [hexContribution_eq_paraf region a h0 (v + hexOmega * du) v (E.pairBase P ++ E.pairLq P)
          (E.pairQ_valid P hP),
        hexContribution_eq_paraf region a h0 (v + hexOmega ^ 2 * du) v (E.pairBase P ++ E.pairLr P)
          (E.pairR_valid P hP)]
    rw [turnCount_append_block a h0 (E.pairBase P) (E.pairLq P),
        turnCount_append_block a h0 (E.pairBase P) (E.pairLr P),
        E.pairLq_sum P hP, E.pairLr_sum P hP]
    have hnr : (ofTurns a h0 (E.pairBase P ++ E.pairLr P)).numVertices
        = (ofTurns a h0 (E.pairBase P ++ E.pairLq P)).numVertices := by
      simp only [numVertices, ofTurns, List.length_append]
      rw [E.pairLen P hP]
    rw [hnr]
    have e2 : ((ofTurns a h0 (E.pairBase P)).turnCount + (-4 : ℤ))
        = (ofTurns a h0 (E.pairBase P)).turnCount - 4 := by ring
    rw [e2]
    simp only [add_sub_cancel_left]
  · 
    apply Finset.sum_congr rfl
    intro T hT
    rw [hexContribution_eq_paraf region a h0 (v + du) v (E.tripBase T) (E.tripP_valid T hT),
        hexContribution_eq_paraf region a h0 (v + hexOmega * du) v (E.tripBase T ++ [-1])
          (E.tripQ_valid T hT),
        hexContribution_eq_paraf region a h0 (v + hexOmega ^ 2 * du) v (E.tripBase T ++ [1])
          (E.tripR_valid T hT)]
    rw [turnCount_concat a h0 (-1) (E.tripBase T), turnCount_concat a h0 1 (E.tripBase T),
        numVertices_concat a h0 (-1) (E.tripBase T), numVertices_concat a h0 1 (E.tripBase T)]
    have e1 : ((ofTurns a h0 (E.tripBase T)).turnCount + (-1 : ℤ))
        = (ofTurns a h0 (E.tripBase T)).turnCount - 1 := by ring
    rw [e1]
    simp only [add_sub_cancel_left]


theorem relation_via_vertexWalkData (E : HexVertexEnumeration region a h0 v du) :
    ((v + du) - v) * parafObservable region a h0 (v + du) (5/8) hexChi
      + ((v + hexOmega * du) - v) * parafObservable region a h0 (v + hexOmega * du) (5/8) hexChi
      + ((v + hexOmega ^ 2 * du) - v)
          * parafObservable region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi = 0 := by
  rw [vertexSum_toVertexWalkData E, VertexWalkData.relation]


end HexVertexEnumeration
end StatMech.Universality

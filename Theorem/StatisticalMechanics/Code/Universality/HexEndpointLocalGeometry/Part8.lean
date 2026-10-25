/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part6


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

@[simp] theorem HexEndpointLocalCrossing.loopCoords_length
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
    (C.loopCoords hlegal).length = C.loopLength := by
  simp [HexEndpointLocalCrossing.loopCoords]


theorem HexEndpointLocalCrossing.loopCoord_injective
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
    Function.Injective (C.loopCoord hlegal.1) := by
  intro i j hij
  apply Fin.ext
  by_contra hval
  have hi : C.index + i.val < ts.length := by
    have := i.isLt
    simp only [HexEndpointLocalCrossing.loopLength] at this
    omega
  have hj : C.index + j.val < ts.length := by
    have := j.isLt
    simp only [HexEndpointLocalCrossing.loopLength] at this
    omega
  have hindex : C.index + i.val ≠ C.index + j.val := by omega
  have hpos := congrArg hexAWPos hij
  simp only [HexEndpointLocalCrossing.loopCoord] at hpos
  rw [← hexEndpointPrefixCoord_pos ts hlegal.1 (C.index + i.val),
    ← hexEndpointPrefixCoord_pos ts hlegal.1 (C.index + j.val)] at hpos
  exact (hexEndpoint_vertexPos_ne_of_saw ts hlegal.2
    (C.index + i.val) (C.index + j.val) hi hj hindex) hpos

theorem HexEndpointLocalCrossing.loopCoords_nodup
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW) :
    (C.loopCoords hlegal.1).Nodup := by
  rw [HexEndpointLocalCrossing.loopCoords, List.nodup_ofFn]
  exact C.loopCoord_injective hlegal


theorem HexEndpointLocalCrossing.loopCoord_zero
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    [NeZero C.loopLength] :
    C.loopCoord hlegal 0 = c := by
  apply hexAWPos_injective
  rw [← C.at_vertex]
  simpa [HexEndpointLocalCrossing.loopCoord, hexJordan_vertexPos] using
    (hexEndpointPrefixCoord_pos ts hlegal C.index).symm


theorem HexEndpointLocalCrossing.finalPrefixCoord_eq
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3) :
    hexEndpointPrefixCoord ts hlegal.1 ts.length = c := by
  apply hexAWPos_injective
  rw [← C.endpoint_lookahead hnotOutside hlegal endEdge hend hcount]
  simpa [hexJordan_vertexPos] using
    (hexEndpointPrefixCoord_pos ts hlegal.1 ts.length).symm


theorem HexEndpointLocalCrossing.loopCoord_cyclic_adjacent
    {ts : List ℤ} {c : HexAWCoord}
    (C : HexEndpointLocalCrossing ts c)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (endEdge : Fin 3)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c endEdge))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 3)
    [NeZero C.loopLength] (i : Fin C.loopLength) :
    ∃ e : Fin 3,
      hexAWNeighbor (C.loopCoord hlegal.1 i) e =
        C.loopCoord hlegal.1 (i + 1) := by
  by_cases hnext : i.val + 1 < C.loopLength
  · have hk : C.index + i.val < ts.length := by
      have := i.isLt
      simp only [HexEndpointLocalCrossing.loopLength] at this hnext
      omega
    obtain ⟨e, he⟩ := hexEndpointPrefixCoord_adjacent ts hlegal.1
      (C.index + i.val) hk
    have hi1 : (i + 1 : Fin C.loopLength) =
        ⟨i.val + 1, hnext⟩ := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one',
        Nat.mod_eq_of_lt (show 1 < C.loopLength by omega),
        Nat.mod_eq_of_lt hnext]
    refine ⟨e, ?_⟩
    rw [hi1]
    simpa [HexEndpointLocalCrossing.loopCoord, Nat.add_assoc] using he
  · have hwrap : i.val + 1 = C.loopLength := by omega
    have hk : C.index + i.val < ts.length := by
      simp only [HexEndpointLocalCrossing.loopLength] at hwrap
      omega
    have hkEnd : C.index + i.val + 1 = ts.length := by
      simp only [HexEndpointLocalCrossing.loopLength] at hwrap
      omega
    obtain ⟨e, he⟩ := hexEndpointPrefixCoord_adjacent ts hlegal.1
      (C.index + i.val) hk
    have hi1 : (i + 1 : Fin C.loopLength) = 0 := by
      apply Fin.ext
      rw [Fin.val_zero, Fin.val_add, Fin.val_one']
      by_cases hOne : C.loopLength = 1
      · simp [hOne]
        exact Nat.mod_one i.val
      · have hOneLt : 1 < C.loopLength := by
          have := C.loopLength_pos
          omega
        rw [Nat.mod_eq_of_lt hOneLt, hwrap, Nat.mod_self]
    refine ⟨e, ?_⟩
    calc
      hexAWNeighbor (C.loopCoord hlegal.1 i) e =
          hexEndpointPrefixCoord ts hlegal.1 ts.length := by
            simpa [HexEndpointLocalCrossing.loopCoord, hkEnd] using he
      _ = c := C.finalPrefixCoord_eq
        hnotOutside hlegal endEdge hend hcount
      _ = C.loopCoord hlegal.1 (i + 1) := by
        rw [hi1]
        exact (C.loopCoord_zero hlegal.1).symm

end
end StatMech.Universality

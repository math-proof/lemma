/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part4


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

theorem hexEndpointPrefixCoord_pos (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) (k : ℕ) :
    hexJordan_vertexPos hexAWStart 1 ts k =
      hexAWPos (hexEndpointPrefixCoord ts hlegal k) := by
  exact Classical.choose_spec (hexEndpoint_vertex_exists_aw (ts.take k) (by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)))


theorem hexEndpointPrefixCoord_adjacent (ts : List ℤ)
    (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1)
    (k : ℕ) (hk : k < ts.length) :
    ∃ e : Fin 3,
      hexAWNeighbor (hexEndpointPrefixCoord ts hlegal k) e =
        hexEndpointPrefixCoord ts hlegal (k + 1) := by
  let ck := hexEndpointPrefixCoord ts hlegal k
  let cn := hexEndpointPrefixCoord ts hlegal (k + 1)
  have hlegalNext : ∀ t ∈ ts.take (k + 1), t = 1 ∨ t = -1 := by
    intro t ht
    exact hlegal t (List.mem_of_mem_take ht)
  have hnpos : hexInfra_midAccum hexAWStart 1 (ts.take (k + 1)) +
      halfStep (hexInfra_headAccum 1 (ts.take (k + 1))) = hexAWPos cn := by
    simpa [hexJordan_vertexPos, cn] using
      hexEndpointPrefixCoord_pos ts hlegal (k + 1)
  obtain ⟨e, hinc⟩ := hexEndpoint_mid_incident_aw
    (ts.take (k + 1)) cn hlegalNext hnpos
  have hcpos : hexInfra_midAccum hexAWStart 1 (ts.take (k + 1)) -
      halfStep (hexInfra_headAccum 1 (ts.take (k + 1))) = hexAWPos ck := by
    have hp := hexEndpoint_vertexPos_eq_nextMid_sub ts k hk
    rw [hexEndpointPrefixCoord_pos ts hlegal k] at hp
    simpa [ck] using hp.symm
  have hbackPos : hexAWPos (hexAWNeighbor cn e) = hexAWPos ck := by
    unfold hexAWMid at hinc
    linear_combination -2 * hinc + hnpos + hcpos
  have hback : hexAWNeighbor cn e = ck := hexAWPos_injective hbackPos
  refine ⟨e, ?_⟩
  have := congrArg (fun d => hexAWNeighbor d e) hback
  simpa [ck, cn] using this.symm


end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Def.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

theorem hexEndpoint_kTwo_mem_cyclicTriplet_aw
    {region : ℂ → Prop} (c : HexAWCoord) (e : Fin 3)
    (base : List ℤ) (t : ℤ)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hneStart : hexAWMid c e ≠ hexAWStart)
    (hvalid : (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW ∧
      (ofTurns hexAWStart 1 (base ++ [t])).StaysIn region ∧
      (ofTurns hexAWStart 1 (base ++ [t])).EndsAt (hexAWMid c e))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) (base ++ [t]) = 2)
    (hall : ∀ f : Fin 3, region (hexAWMid c f)) :
    ∃ C : HexEndpointCyclicTriplet region hexAWStart 1
        (hexAWPos c) (hexAWMid c 0 - hexAWPos c),
      base ++ [t] ∈ C.piece ∧ C.base = base := by
  have hlast := hexEndpoint_kTwo_last_vertex_aw base t c e
    hnotOutside hvalid.1 hvalid.2.2 hneStart hcount
  have hnew := hexEndpoint_final_mid_fresh_aw base t c e
    hvalid.1 hvalid.2.2 hneStart
  have hvalid' :
      (ofTurns hexAWStart 1 (base ++ [t])).EndpointIsLegalSAW ∧
        (ofTurns hexAWStart 1 (base ++ [t])).StaysIn region ∧
        (ofTurns hexAWStart 1 (base ++ [t])).EndsAt
          (labelMid (hexAWPos c)
            (hexAWMid c 0 - hexAWPos c) e) := by
    simpa only [hexAW_labelMid_eq_mid] using hvalid
  have hnew' : ¬PassesThrough hexAWStart 1 base
      (labelMid (hexAWPos c) (hexAWMid c 0 - hexAWPos c) e) := by
    simpa only [hexAW_labelMid_eq_mid] using hnew
  have hall' : ∀ f : Fin 3,
      region (labelMid (hexAWPos c)
        (hexAWMid c 0 - hexAWPos c) f) := by
    intro f
    simpa only [hexAW_labelMid_eq_mid] using hall f
  exact hexEndpoint_kTwo_mem_cyclicTriplet e base t
    (hexAW_base_du_ne_zero c) hvalid' hcount hlast hnew' hall'


end
end StatMech.Universality

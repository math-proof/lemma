/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointLocalGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointVertex.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexBrickUmlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part2


namespace StatMech.Universality

open Complex Function HexWalk

noncomputable section

def hexEndpoint_count_one_launch_aw
    (ts : List ℤ) (c : HexAWCoord) (e : Fin 3)
    (hnotOutside : c ≠ hexAWNeighbor hexAWOriginCoord 0)
    (hlegal : (ofTurns hexAWStart 1 ts).EndpointIsLegalSAW)
    (hend : (ofTurns hexAWStart 1 ts).EndsAt (hexAWMid c e))
    (hcount : specialMidCount hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) ts = 1) :
    HexCyclicLaunch hexAWStart 1 (hexAWPos c)
      (hexAWMid c 0 - hexAWPos c) e ts where
  endsAt := by
    simpa only [hexAW_labelMid_eq_mid] using hend
  lastVertex := by
    rw [hexAW_labelMid_eq_mid]
    have hmid : hexInfra_midAccum hexAWStart 1 ts = hexAWMid c e := by
      rw [← hexInfra_endMid_eq_midAccum]
      exact hend
    rw [← hmid]
    exact hexEndpoint_count_one_forward_vertex_aw
      ts c e hnotOutside hlegal hend hcount


end
end StatMech.Universality

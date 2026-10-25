/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWColumns.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWAugment.Part14
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits.Part6
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhc_prefixCoord_vertex (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns) (k : ℕ) :
    hexInfra_midAccum hexAWStart 1 (ts.take k) +
        halfStep (hexInfra_headAccum 1 (ts.take k)) =
      hexAWPos (hlhc_prefixCoord ts hlegal k) := by
  unfold hlhc_prefixCoord
  exact Classical.choose_spec (hexEndpoint_vertex_exists_aw (ts.take k)
    (by
      intro t ht
      exact hlegal t (List.mem_of_mem_take ht)))

theorem hlhc_prefixCoord_mid_incident (ts : List ℤ)
    (hlegal : (ofTurns hexAWStart 1 ts).LegalTurns) (k : ℕ) :
    ∃ e : Fin 3,
      hexInfra_midAccum hexAWStart 1 (ts.take k) =
        hexAWMid (hlhc_prefixCoord ts hlegal k) e := by
  apply hexEndpoint_mid_incident_aw
  · intro t ht
    exact hlegal t (List.mem_of_mem_take ht)
  · exact hlhc_prefixCoord_vertex ts hlegal k


end
end StatMech.Universality

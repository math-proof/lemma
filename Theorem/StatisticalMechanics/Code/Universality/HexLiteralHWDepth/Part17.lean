/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part15


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hlhd_intervalRaw_vertices_pos (ts : List ℤ)
    (hleg : (ofTurns hexAWStart 1 ts).IsLegalSAW)
    (hhalf : HLHDLiteralHalfSpace ts hleg)
    (p : ℕ × ℕ) (hp : p ∈ hlhd_intervals ts hleg) :
    verticesAux
        (hexInfra_midAccum hexAWStart 1 (ts.take p.1))
        (hexInfra_headAccum 1 (ts.take p.1))
        (hlhd_intervalRaw ts p) =
      (hlhd_intervalCoords ts hleg p).map hexAWPos := by
  apply List.ext_getElem
  · simp [hlhd_intervalCoords, length_verticesAux]
  · intro r hr hr'
    have hrle : r ≤ (hlhd_intervalRaw ts p).length := by
      rw [length_verticesAux] at hr
      omega
    have hget := hexJordan_verticesAux_getElem?_eq
      (hexInfra_midAccum hexAWStart 1 (ts.take p.1))
      (hexInfra_headAccum 1 (ts.take p.1))
      (hlhd_intervalRaw ts p) r hrle
    rw [List.getElem?_eq_getElem hr, Option.some.injEq] at hget
    rw [List.getElem_map]
    unfold hlhd_intervalCoords
    rw [List.getElem_ofFn]
    rw [hget]
    change hexJordan_vertexPos
        (hexInfra_midAccum hexAWStart 1 (ts.take p.1))
        (hexInfra_headAccum 1 (ts.take p.1))
        (hlhd_intervalRaw ts p) r =
      hexAWPos (hlhc_prefixCoord ts hleg.1 (p.1 + r))
    rw [hlhd_intervalRaw_vertexPos ts hleg hhalf p hp r hrle]
    exact hlhc_prefixCoord_vertex ts hleg.1 (p.1 + r)

end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripAssembly.Part14
import Def.StatisticalMechanics.Code.Universality.HexCorrectedStripLimits


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators

noncomputable section

theorem hexCSSideWalk_mono
    {T T' L L' : ℕ} {hpos : 0 < T} {hpos' : 0 < T'}
    (hT : T ≤ T') (hL : L ≤ L') {ts : List ℤ}
    (hwalk : HexCSSideWalk T L hpos ts) :
    HexCSSideWalk T' L' hpos' ts := by
  rcases hwalk with ⟨hlegal, hstay, c, hc, hcolor, hdepth, hne, hend⟩
  exact ⟨hlegal, endpointStaysIn_mono
      (hexCSFiniteRegion_mono hT hL) hstay,
    c, hexCSVertexSet_mono hT hL hc, hcolor, hdepth, hne, hend⟩

theorem hexCSTopWalk_mono_L
    {T L L' : ℕ} {hpos : 0 < T} (hL : L ≤ L') {ts : List ℤ}
    (hwalk : HexCSTopWalk T L hpos ts) :
    HexCSTopWalk T L' hpos ts := by
  rcases hwalk with ⟨hlegal, hstay, c, hc, hcolor, hdepth, hend⟩
  exact ⟨hlegal, endpointStaysIn_mono
      (hexCSFiniteRegion_mono le_rfl hL) hstay,
    c, hexCSVertexSet_mono le_rfl hL hc, hcolor, hdepth, hend⟩


end
end StatMech.Universality

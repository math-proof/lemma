/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripNormalizedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalization.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripEnum.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexStripInterior.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary


namespace StatMech.Universality

open Complex HexWalk


namespace HexFiniteRegion

theorem not_startInteriorUnique (R : HexFiniteRegion) (h0 : ℤ) :
    ¬R.StartInteriorUnique h0 := by
  intro hstart
  have hstay :
      (ofTurns R.start (h0 + 1) []).StaysIn R.inRegion := by
    intro m hm
    change m ∈ R.mids
    have hmids : (ofTurns R.start (h0 + 1) []).mids = [R.start] := by
      show (trivialWalk R.start (h0 + 1)).mids = [R.start]
      unfold HexWalk.mids
      simp [trivialWalk]
    rw [hmids] at hm
    have hma : m = R.start := List.mem_singleton.mp hm
    exact hma ▸ R.start_mem
  have hmem : R.start + halfStep (h0 + 1) ∈ R.verts := by
    apply R.vertices_mem R.start (h0 + 1) [] hstay
    change R.start + halfStep (h0 + 1) ∈
      [R.start + halfStep (h0 + 1)]
    exact List.mem_singleton.mpr rfl
  have heq := hstart (h0 + 1) hmem
  have hstep : halfStep (h0 + 1) = halfStep h0 := add_left_cancel heq
  have hdiv : (6 : ℤ) ∣ (h0 + 1 - h0) :=
    (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj hstep)
  norm_num at hdiv


theorem hexStrip_finiteRegion_not_startInteriorUnique
    (M : Finset ℂ) (a : ℂ) (ha : a ∈ M) (h0 : ℤ) :
    ¬(hexStrip_finiteRegion M a ha).StartInteriorUnique h0 := by
  intro hstart
  have hmem :
      a + halfStep (h0 + 1) ∈
        (hexStrip_finiteRegion M a ha).verts := by
    rw [hexStrip_finiteRegion_verts]
    exact hexStrip_mem_verts M ha (h0 + 1)
  have heq := hstart (h0 + 1) hmem
  have hstep : halfStep (h0 + 1) = halfStep h0 := by
    exact add_left_cancel heq
  have hdiv : (6 : ℤ) ∣ (h0 + 1 - h0) :=
    (hexUnit_eq_iff_mod _ _).mp (hexInfra_halfStep_inj hstep)
  norm_num at hdiv


end HexFiniteRegion
end StatMech.Universality

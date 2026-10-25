/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeSourceArc
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction.Part2
import Def.StatisticalMechanics.Code.Universality.RSWSourceArcPlacement
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_relaxedLocalTraceArcExists_iff_not_defectCut
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) :
    RlcRelaxedLocalTraceArcExists G omega ↔
      ¬ RlcRelaxedLocalDefectsSeparateTraces G omega := by
  constructor
  · rintro ⟨x, y, a, hxPath, hyPath, hlocal⟩ hcut
    obtain ⟨f, g, hfg, hbad⟩ := hcut a hxPath hyPath
    exact hbad (hlocal hfg)
  · intro hcut
    unfold RlcRelaxedLocalDefectsSeparateTraces at hcut
    push Not at hcut
    obtain ⟨x, y, a, hxPath, hyPath, hlocal⟩ := hcut
    exact ⟨x, y, a, hxPath, hyPath,
      fun {_ _} hfg => hlocal _ _ hfg⟩


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalTraceArc
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (h : RlcRelaxedLocalTraceArcExists G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨x, y, a, hxPath, hyPath, hlocal⟩ := h
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
    G hn hlt omega a hxPath hyPath hlocal


theorem rlc_relaxedLocalDefectsSeparateTraces_of_dualReflect_failure
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : rlc_dualReflectConfig omega ∉
      rlc_mixedWiredConnectorEvent G) :
    RlcRelaxedLocalDefectsSeparateTraces G omega := by
  intro x y a hxPath hyPath
  by_contra hdefect
  have hlocal : ∀ {f g : Site 2}, s(f, g) ∈ a.edges →
      rlc_contourEdgeRelaxedLocal G f g := by
    intro f g hfg
    by_contra hbad
    exact hdefect ⟨f, g, hfg, hbad⟩
  exact hno
    (rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
      G hn hlt omega a hxPath hyPath hlocal)


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_not_defectCut
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hcut : ¬ RlcRelaxedLocalDefectsSeparateTraces G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  unfold RlcRelaxedLocalDefectsSeparateTraces at hcut
  push Not at hcut
  obtain ⟨x, y, a, hxPath, hyPath, hlocal⟩ := hcut
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
    G hn hlt omega a hxPath hyPath
      (fun {_ _} hfg => hlocal _ _ hfg)


end Universality
end StatMech

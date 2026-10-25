/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWSourceArcPlacement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeSourceArc
import Theorem.StatisticalMechanics.Code.Universality.RSWAxisOrContactObstruction.Part2
import Def.StatisticalMechanics.Code.Universality.RSWSourceArcPlacement.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_carriesRelaxedTraceArc_iff_not_defectsHitTraceSubwalksOf
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma')
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v) :
    RlcFaceBoundaryWalkCarriesRelaxedTraceArc G omega p ↔
      ¬ RlcRelaxedLocalDefectsHitTraceSubwalksOf G omega p := by
  classical
  constructor
  · rintro ⟨x, y, a, hsub, hx, hy, hlocal⟩ hhit
    obtain ⟨f, g, hfg, hbad⟩ := hhit a hsub hx hy
    exact hbad (hlocal hfg)
  · intro hnot
    unfold RlcRelaxedLocalDefectsHitTraceSubwalksOf at hnot
    push Not at hnot
    obtain ⟨x, y, a, hsub, hx, hy, hlocal⟩ := hnot
    exact ⟨x, y, a, hsub, hx, hy,
      fun {_ _} hfg => hlocal _ _ hfg⟩


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_carriesRelaxedTraceArc
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2))) {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v)
    (hcarry : RlcFaceBoundaryWalkCarriesRelaxedTraceArc G omega p) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨x, y, a, _hsub, hx, hy, hlocal⟩ := hcarry
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_relaxedLocalArc
    G hn hlt omega a hx hy hlocal


theorem RlcRelaxedLocalDefectsSeparateTraces.hitTraceSubwalksOf
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {G : RlcAxisBarrierGap gamma gamma'}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hcut : RlcRelaxedLocalDefectsSeparateTraces G omega)
    {u v : Site 2}
    (p : (faceBoundaryGraph
      (rlc_mixedWiredReachSet G omega)).Walk u v) :
    RlcRelaxedLocalDefectsHitTraceSubwalksOf G omega p := by
  intro x y a _hsub hxPath hyPath
  exact hcut a hxPath hyPath


end Universality
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKTorusSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Theorem.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part10
import Theorem.StatisticalMechanics.Code.FK.ActiveEdges.Part4
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part15


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem triangularTorusSectorTwoPointObservable_eq_indicator
    (L : ℕ) [Fact (2 < L)] (x y : TorusSite L)
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    triangularTorusSectorObservable L
        (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) omega =
      triangularTorusActiveTwoPointIndicator L x y omega := by
  classical
  unfold triangularTorusSectorObservable triHexFKTerminalTwoPointObservable
    triangularTorusActiveTwoPointIndicator
  change (if (triangularTorusTerminalSectorGraph L omega).Reachable x y then
      (1 : ℝ) else 0) =
    if (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y then 1 else 0
  have hiff := triangularTorus_openSub_reachable_iff_terminalSectorGraph
    L omega x y
  by_cases h : (openSub (triangularTorusGraph L)
      (extendActive (triangularTorusGraph L) omega)).Reachable x y
  · have hs := hiff.mp h
    simp [h, hs]
  · have hs : ¬ (triangularTorusTerminalSectorGraph L omega).Reachable x y :=
      fun hs => h (hiff.mpr hs)
    simp [h, hs]

theorem hexagonalTorusSectorTwoPointObservable_eq_indicator
    (L : ℕ) [Fact (2 < L)] (x y : TorusSite L)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    hexagonalTorusSectorObservable L
        (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) omega =
      hexagonalTorusActiveWhiteTwoPointIndicator L x y omega := by
  classical
  unfold hexagonalTorusSectorObservable triHexFKTerminalTwoPointObservable
    hexagonalTorusActiveWhiteTwoPointIndicator
  change (if (hexagonalTorusTerminalSectorGraph L omega).Reachable x y then
      (1 : ℝ) else 0) =
    if (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable
        (x, true) (y, true) then 1 else 0
  have hiff := hexagonalTorus_openSub_white_reachable_iff_terminalSectorGraph
    L omega x y
  by_cases h : (openSub (hexagonalTorusGraph L)
      (extendActive (hexagonalTorusGraph L) omega)).Reachable (x, true) (y, true)
  · have hs := hiff.mp h
    simp [h, hs]
  · have hs : ¬ (hexagonalTorusTerminalSectorGraph L omega).Reachable x y :=
      fun hs => h (hiff.mpr hs)
    simp [h, hs]


theorem triHexFK_torus_activeTwoPointRatio_eq
    (L : ℕ) [Fact (2 < L)]
    (pfTri : Sym2 (TorusSite L) → ℝ)
    (pfStar : Sym2 (HexTorusVertex L) → ℝ)
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (hpfTri : ∀ e : (triangularTorusGraph L).edgeSet, pfTri e.1 ≠ 1)
    (hpfStar : ∀ e : (hexagonalTorusGraph L).edgeSet, pfStar e.1 ≠ 1)
    (hoddsTri : ∀ e : (triangularTorusGraph L).edgeSet,
      pfTri e.1 = (1 - pfTri e.1) *
        triangularTorusSweepEdgeOdds L y0 y1 y2 e)
    (hoddsStar : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pfStar e.1 = (1 - pfStar e.1) *
        hexagonalTorusSweepEdgeOdds L y0Star y1Star y2Star e)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (x y : TorusSite L) :
    activeNumer (hexagonalTorusGraph L) pfStar q
        (hexagonalTorusActiveWhiteTwoPointIndicator L x y) /
        activeZ (hexagonalTorusGraph L) pfStar q =
      activeNumer (triangularTorusGraph L) pfTri q
        (triangularTorusActiveTwoPointIndicator L x y) /
        activeZ (triangularTorusGraph L) pfTri q := by
  have hratio := triHexFK_torus_activeSectorRatio_eq L pfTri pfStar
    hq hyprod hpfTri hpfStar hoddsTri hoddsStar h0 h1 h2 hsurface
    (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y)
  have htri : triangularTorusSectorObservable L
      (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) =
        triangularTorusActiveTwoPointIndicator L x y := by
    funext omega
    exact triangularTorusSectorTwoPointObservable_eq_indicator L x y omega
  have hstar : hexagonalTorusSectorObservable L
      (triHexFKTerminalTwoPointObservable (triHexTorusCellTerminal L) x y) =
        hexagonalTorusActiveWhiteTwoPointIndicator L x y := by
    funext omega
    exact hexagonalTorusSectorTwoPointObservable_eq_indicator L x y omega
  simpa [htri, hstar] using hratio

end StatMech.FK.PeriodicPlanar

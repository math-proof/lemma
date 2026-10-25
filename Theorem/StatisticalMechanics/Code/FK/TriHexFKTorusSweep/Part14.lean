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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part14


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem triangularTorus_activeNumer_sector_eq
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (TorusSite L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (triangularTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e)
    (observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ) :
    activeNumer (triangularTorusGraph L) pf q
        (triangularTorusSectorObservable L observable) =
      (∏ e : (triangularTorusGraph L).edgeSet, (1 - pf e.1)) *
        triangleFKGlobalConfigSum y0 y1 y2
          (fun sector => triHexTorusSectorClusterWeight L q sector *
            observable sector) := by
  classical
  unfold activeNumer triangleFKGlobalConfigSum triangularTorusSectorObservable
  rw [← (triangularTorusActiveConfigEquiv L).symm.sum_comp
    (fun omega => observable (fun z => triangleFKLocalConnectivity
      (triangularTorusActiveConfigEquiv L omega z)) *
        activeWeight (triangularTorusGraph L) pf q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triangularTorus_activeWeight_eq_closedProduct_mul_cellWeight
    L pf q y0 y1 y2 hodds]
  rw [(triangularTorusActiveConfigEquiv L).apply_symm_apply config]
  ring


theorem hexagonalTorus_activeNumer_sector_eq
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (HexTorusVertex L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * hexagonalTorusSweepEdgeOdds L y0 y1 y2 e)
    (observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ) :
    activeNumer (hexagonalTorusGraph L) pf q
        (hexagonalTorusSectorObservable L observable) =
      (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pf e.1)) *
        starFKGlobalConfigSum q y0 y1 y2
          (fun sector => triHexTorusSectorClusterWeight L q sector *
            observable sector) := by
  classical
  unfold activeNumer starFKGlobalConfigSum hexagonalTorusSectorObservable
  rw [← (hexagonalTorusActiveConfigEquiv L).symm.sum_comp
    (fun omega => observable (fun z => starFKLocalConnectivity
      (hexagonalTorusActiveConfigEquiv L omega z)) *
        activeWeight (hexagonalTorusGraph L) pf q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [hexagonalTorus_activeWeight_eq_closedProduct_mul_cellWeight
    L pf q y0 y1 y2 hodds]
  rw [(hexagonalTorusActiveConfigEquiv L).apply_symm_apply config]
  ring


theorem triHexFK_torus_activeSectorRatio_eq
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
    (observable : (TorusSite L → ThreeTerminalConnectivity) → ℝ) :
    activeNumer (hexagonalTorusGraph L) pfStar q
        (hexagonalTorusSectorObservable L observable) /
        activeZ (hexagonalTorusGraph L) pfStar q =
      activeNumer (triangularTorusGraph L) pfTri q
        (triangularTorusSectorObservable L observable) /
        activeZ (triangularTorusGraph L) pfTri q := by
  have hclosedTri :
      (∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro e _
    exact sub_ne_zero.mpr (Ne.symm (hpfTri e))
  have hclosedStar :
      (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro e _
    exact sub_ne_zero.mpr (Ne.symm (hpfStar e))
  rw [hexagonalTorus_activeNumer_sector_eq L pfStar q y0Star y1Star y2Star
      hoddsStar observable,
    hexagonalTorus_activeZ_eq_closedProduct_mul_globalConfigSum
      L pfStar q y0Star y1Star y2Star hoddsStar,
    triangularTorus_activeNumer_sector_eq L pfTri q y0 y1 y2 hoddsTri observable,
    triangularTorus_activeZ_eq_closedProduct_mul_globalConfigSum
      L pfTri q y0 y1 y2 hoddsTri]
  rw [mul_div_mul_left _ _ hclosedStar, mul_div_mul_left _ _ hclosedTri]
  rw [starFKGlobalConfigSum_eq_sweepSum,
    starFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum]
  exact triHexFK_globalSweepRatio_eq hq hyprod h0 h1 h2 hsurface
    (triHexTorusSectorClusterWeight L q) observable


end StatMech.FK.PeriodicPlanar

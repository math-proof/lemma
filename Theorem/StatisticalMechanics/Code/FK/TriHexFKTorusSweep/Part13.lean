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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part13


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem triangularTorus_activeWeight_eq_closedProduct_mul_cellWeight
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (TorusSite L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (triangularTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e)
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    activeWeight (triangularTorusGraph L) pf q omega =
      (∏ e : (triangularTorusGraph L).edgeSet, (1 - pf e.1)) *
        (triHexTorusSectorClusterWeight L q
            (fun z => triangleFKLocalConnectivity
              (triangularTorusActiveConfigEquiv L omega z)) *
          ∏ z, triangleFKLocalOddsWeight y0 y1 y2
            (triangularTorusActiveConfigEquiv L omega z)) := by
  unfold activeWeight fkWeightW triHexTorusSectorClusterWeight
  rw [edgeProductW_extendActive_odds_factor _ _ _ hodds,
    triangularTorus_numClusters_eq_terminalSector,
    ← triangularTorus_localOddsProduct_eq_activeOddsProduct]
  unfold triangularTorusTerminalSectorGraph
  ring


theorem hexagonalTorus_activeWeight_eq_closedProduct_mul_cellWeight
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (HexTorusVertex L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * hexagonalTorusSweepEdgeOdds L y0 y1 y2 e)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    activeWeight (hexagonalTorusGraph L) pf q omega =
      (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pf e.1)) *
        (triHexTorusSectorClusterWeight L q
            (fun z => starFKLocalConnectivity
              (hexagonalTorusActiveConfigEquiv L omega z)) *
          ∏ z, starFKLocalOddsWeight q y0 y1 y2
            (hexagonalTorusActiveConfigEquiv L omega z)) := by
  unfold activeWeight fkWeightW triHexTorusSectorClusterWeight
  rw [edgeProductW_extendActive_odds_factor _ _ _ hodds,
    hexagonalTorus_numClusters_eq_terminalSector_add_isolated,
    pow_add, ← hexagonalTorus_isolatedCenterFactor_product,
    hexagonalTorus_localOddsProduct_eq_activeOddsProduct]
  unfold hexagonalTorusTerminalSectorGraph
  ring


theorem triangularTorus_activeZ_eq_closedProduct_mul_globalConfigSum
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (TorusSite L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (triangularTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * triangularTorusSweepEdgeOdds L y0 y1 y2 e) :
    activeZ (triangularTorusGraph L) pf q =
      (∏ e : (triangularTorusGraph L).edgeSet, (1 - pf e.1)) *
        triangleFKGlobalConfigSum y0 y1 y2
          (triHexTorusSectorClusterWeight L q) := by
  classical
  unfold activeZ triangleFKGlobalConfigSum
  rw [← (triangularTorusActiveConfigEquiv L).symm.sum_comp
    (fun omega => activeWeight (triangularTorusGraph L) pf q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [triangularTorus_activeWeight_eq_closedProduct_mul_cellWeight
    L pf q y0 y1 y2 hodds]
  rw [(triangularTorusActiveConfigEquiv L).apply_symm_apply config]


theorem hexagonalTorus_activeZ_eq_closedProduct_mul_globalConfigSum
    (L : ℕ) [Fact (2 < L)] (pf : Sym2 (HexTorusVertex L) → ℝ)
    (q y0 y1 y2 : ℝ)
    (hodds : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pf e.1 = (1 - pf e.1) * hexagonalTorusSweepEdgeOdds L y0 y1 y2 e) :
    activeZ (hexagonalTorusGraph L) pf q =
      (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pf e.1)) *
        starFKGlobalConfigSum q y0 y1 y2
          (triHexTorusSectorClusterWeight L q) := by
  classical
  unfold activeZ starFKGlobalConfigSum
  rw [← (hexagonalTorusActiveConfigEquiv L).symm.sum_comp
    (fun omega => activeWeight (hexagonalTorusGraph L) pf q omega)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro config _
  rw [hexagonalTorus_activeWeight_eq_closedProduct_mul_cellWeight
    L pf q y0 y1 y2 hodds]
  rw [(hexagonalTorusActiveConfigEquiv L).apply_symm_apply config]


theorem triHexFK_globalConfigSum_identity
    {I : Type*} [Fintype I] [DecidableEq I]
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (external : (I → ThreeTerminalConnectivity) → ℝ) :
    (y0 * y1 * y2) ^ Fintype.card I *
        starFKGlobalConfigSum q y0Star y1Star y2Star external =
      (q ^ 2) ^ Fintype.card I *
        triangleFKGlobalConfigSum y0 y1 y2 external := by
  rw [starFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum]
  exact triHexFK_globalSweepSum_identity h0 h1 h2 hsurface external


theorem triHexFK_torus_activeZ_identity
    (L : ℕ) [Fact (2 < L)]
    (pfTri : Sym2 (TorusSite L) → ℝ)
    (pfStar : Sym2 (HexTorusVertex L) → ℝ)
    {q y0 y1 y2 y0Star y1Star y2Star : ℝ}
    (hoddsTri : ∀ e : (triangularTorusGraph L).edgeSet,
      pfTri e.1 = (1 - pfTri e.1) *
        triangularTorusSweepEdgeOdds L y0 y1 y2 e)
    (hoddsStar : ∀ e : (hexagonalTorusGraph L).edgeSet,
      pfStar e.1 = (1 - pfStar e.1) *
        hexagonalTorusSweepEdgeOdds L y0Star y1Star y2Star e)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0) :
    (y0 * y1 * y2) ^ Fintype.card (TorusSite L) *
        (∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
          activeZ (hexagonalTorusGraph L) pfStar q =
      (q ^ 2) ^ Fintype.card (TorusSite L) *
        (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1)) *
          activeZ (triangularTorusGraph L) pfTri q := by
  rw [triangularTorus_activeZ_eq_closedProduct_mul_globalConfigSum
      L pfTri q y0 y1 y2 hoddsTri,
    hexagonalTorus_activeZ_eq_closedProduct_mul_globalConfigSum
      L pfStar q y0Star y1Star y2Star hoddsStar]
  have hglobal := triHexFK_globalConfigSum_identity
    (I := TorusSite L) h0 h1 h2 hsurface (triHexTorusSectorClusterWeight L q)
  calc
    (y0 * y1 * y2) ^ Fintype.card (TorusSite L) *
        (∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
        ((∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1)) *
          starFKGlobalConfigSum q y0Star y1Star y2Star
            (triHexTorusSectorClusterWeight L q)) =
      ((∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
        (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1))) *
          ((y0 * y1 * y2) ^ Fintype.card (TorusSite L) *
            starFKGlobalConfigSum q y0Star y1Star y2Star
              (triHexTorusSectorClusterWeight L q)) := by ring
    _ = ((∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
        (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1))) *
          ((q ^ 2) ^ Fintype.card (TorusSite L) *
            triangleFKGlobalConfigSum y0 y1 y2
              (triHexTorusSectorClusterWeight L q)) := by rw [hglobal]
    _ = (q ^ 2) ^ Fintype.card (TorusSite L) *
        (∏ e : (hexagonalTorusGraph L).edgeSet, (1 - pfStar e.1)) *
          ((∏ e : (triangularTorusGraph L).edgeSet, (1 - pfTri e.1)) *
            triangleFKGlobalConfigSum y0 y1 y2
              (triHexTorusSectorClusterWeight L q)) := by ring


end StatMech.FK.PeriodicPlanar

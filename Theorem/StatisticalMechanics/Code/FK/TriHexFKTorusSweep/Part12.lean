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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part12


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem triangularTorus_localOddsProduct_eq_activeOddsProduct
    (L : ℕ) [Fact (2 < L)] (y0 y1 y2 : ℝ)
    (omega : ConfigSpace (triangularTorusGraph L).edgeSet) :
    (∏ z, triangleFKLocalOddsWeight y0 y1 y2
      (triangularTorusActiveConfigEquiv L omega z)) =
        ∏ e : (triangularTorusGraph L).edgeSet,
          if omega e then triangularTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
  rw [triangleFKGlobalLocalOdds_eq_directionProduct]
  calc
    (∏ a : TorusSite L × Fin 3,
        if triHexLocalDirection (triangularTorusActiveConfigEquiv L omega a.1) a.2 then
          triHexDirectionOdds y0 y1 y2 a.2 else 1) =
      ∏ a : TriHexTorusEdgeIndex L,
        if omega (triHexTorusTriangleSweepEdgeEquiv L a) then
          triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
      apply Fintype.prod_congr
      rintro ⟨z, i⟩
      fin_cases i <;> rfl
    _ = ∏ e : (triangularTorusGraph L).edgeSet,
          if omega e then triangularTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
      simpa [triangularTorusSweepEdgeOdds] using
        (triHexTorusTriangleSweepEdgeEquiv L).prod_comp
          (fun e => if omega e then
            triangularTorusSweepEdgeOdds L y0 y1 y2 e else 1)

theorem hexagonalTorus_localOddsProduct_eq_activeOddsProduct
    (L : ℕ) [Fact (2 < L)] (q y0 y1 y2 : ℝ)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    (∏ z, starFKLocalOddsWeight q y0 y1 y2
      (hexagonalTorusActiveConfigEquiv L omega z)) =
      (∏ z, starFKIsolatedCenterFactor q
        (hexagonalTorusActiveConfigEquiv L omega z)) *
        ∏ e : (hexagonalTorusGraph L).edgeSet,
          if omega e then hexagonalTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
  rw [starFKGlobalLocalOdds_eq_isolated_mul_directionProduct]
  congr 1
  calc
    (∏ a : TorusSite L × Fin 3,
        if triHexLocalDirection (hexagonalTorusActiveConfigEquiv L omega a.1) a.2 then
          triHexDirectionOdds y0 y1 y2 a.2 else 1) =
      ∏ a : TriHexTorusEdgeIndex L,
        if omega (triHexTorusStarSweepEdgeEquiv L a) then
          triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
      apply Fintype.prod_congr
      rintro ⟨z, i⟩
      fin_cases i <;> rfl
    _ = ∏ e : (hexagonalTorusGraph L).edgeSet,
          if omega e then hexagonalTorusSweepEdgeOdds L y0 y1 y2 e else 1 := by
      simpa [hexagonalTorusSweepEdgeOdds] using
        (triHexTorusStarSweepEdgeEquiv L).prod_comp
          (fun e => if omega e then
            hexagonalTorusSweepEdgeOdds L y0 y1 y2 e else 1)


theorem fintype_prod_ite_eq_pow_card_subtype
    {I : Type*} [Fintype I] (P : I → Prop) [DecidablePred P]
    [Fintype {i // P i}] (q : ℝ) :
    (∏ i, if P i then q else 1) = q ^ Fintype.card {i // P i} := by
  classical
  rw [Fintype.card_subtype P]
  change Finset.univ.prod (fun i => if P i then q else 1) = _
  rw [Finset.prod_ite]
  simp


theorem hexagonalTorus_isolatedCenterFactor_product
    (L : ℕ) [Fact (2 < L)] (q : ℝ)
    (omega : ConfigSpace (hexagonalTorusGraph L).edgeSet) :
    (∏ z, starFKIsolatedCenterFactor q
      (hexagonalTorusActiveConfigEquiv L omega z)) =
        q ^ Fintype.card (HexagonalTorusIsolatedCenter L omega) := by
  unfold starFKIsolatedCenterFactor HexagonalTorusIsolatedCenter
  exact @fintype_prod_ite_eq_pow_card_subtype (TorusSite L) inferInstance
    (fun z => hexagonalTorusActiveConfigEquiv L omega z =
      (false, false, false)) inferInstance
    (hexagonalTorusIsolatedCenterFintype L omega) q


end StatMech.FK.PeriodicPlanar

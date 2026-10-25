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
import Def.StatisticalMechanics.Code.FK.TriHexFKTorusSweep.Part11


namespace StatMech.FK.PeriodicPlanar

open Universality

open scoped BigOperators


theorem triangleFKLocalOddsWeight_eq_directionProduct
    (y0 y1 y2 : ℝ) (config : LocalConfig) :
    triangleFKLocalOddsWeight y0 y1 y2 config =
      ∏ i : Fin 3, if triHexLocalDirection config i then
        triHexDirectionOdds y0 y1 y2 i else 1 := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [triangleFKLocalOddsWeight, triHexLocalDirection,
      triHexDirectionOdds, Fin.prod_univ_succ] <;> ring

theorem starFKLocalOddsWeight_eq_isolated_mul_directionProduct
    (q y0 y1 y2 : ℝ) (config : LocalConfig) :
    starFKLocalOddsWeight q y0 y1 y2 config =
      starFKIsolatedCenterFactor q config *
        ∏ i : Fin 3, if triHexLocalDirection config i then
          triHexDirectionOdds y0 y1 y2 i else 1 := by
  rcases config with ⟨b0, b1, b2⟩
  fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;>
    simp [starFKLocalOddsWeight, starFKIsolatedCenterFactor,
      triHexLocalDirection, triHexDirectionOdds, Fin.prod_univ_succ] <;> ring

theorem triangleFKGlobalLocalOdds_eq_directionProduct
    {I : Type*} [Fintype I] (y0 y1 y2 : ℝ)
    (config : I → LocalConfig) :
    (∏ z, triangleFKLocalOddsWeight y0 y1 y2 (config z)) =
      ∏ a : I × Fin 3, if triHexLocalDirection (config a.1) a.2 then
        triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
  rw [Fintype.prod_prod_type]
  apply Fintype.prod_congr
  intro z
  exact triangleFKLocalOddsWeight_eq_directionProduct y0 y1 y2 (config z)

theorem starFKGlobalLocalOdds_eq_isolated_mul_directionProduct
    {I : Type*} [Fintype I] (q y0 y1 y2 : ℝ)
    (config : I → LocalConfig) :
    (∏ z, starFKLocalOddsWeight q y0 y1 y2 (config z)) =
      (∏ z, starFKIsolatedCenterFactor q (config z)) *
        ∏ a : I × Fin 3, if triHexLocalDirection (config a.1) a.2 then
          triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
  calc
    (∏ z, starFKLocalOddsWeight q y0 y1 y2 (config z)) =
        ∏ z, starFKIsolatedCenterFactor q (config z) *
          (∏ i : Fin 3, if triHexLocalDirection (config z) i then
            triHexDirectionOdds y0 y1 y2 i else 1) := by
      apply Fintype.prod_congr
      intro z
      exact starFKLocalOddsWeight_eq_isolated_mul_directionProduct
        q y0 y1 y2 (config z)
    _ = (∏ z, starFKIsolatedCenterFactor q (config z)) *
        ∏ z, ∏ i : Fin 3, if triHexLocalDirection (config z) i then
          triHexDirectionOdds y0 y1 y2 i else 1 := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ z, starFKIsolatedCenterFactor q (config z)) *
        ∏ a : I × Fin 3, if triHexLocalDirection (config a.1) a.2 then
          triHexDirectionOdds y0 y1 y2 a.2 else 1 := by
      rw [Fintype.prod_prod_type]


end StatMech.FK.PeriodicPlanar

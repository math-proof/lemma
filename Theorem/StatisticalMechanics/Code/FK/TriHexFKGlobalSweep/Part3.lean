/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKGlobalSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKExternalWeight
import Def.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part3
open Finset
open scoped BigOperators


namespace StatMech.FK.PeriodicPlanar

open Universality


theorem triHexFK_globalSweep_sector_identity
    {ι : Type*} [Fintype ι]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (sector : ι → ThreeTerminalConnectivity) :
    (y0 * y1 * y2) ^ Fintype.card ι *
        (∏ i, starFKTerminalWeight q y0Star y1Star y2Star (sector i)) =
      (q ^ 2) ^ Fintype.card ι *
        ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i) := by
  classical
  have hprod := Finset.prod_congr rfl fun i (_hi : i ∈ (univ : Finset ι)) =>
    triHexFK_terminalWeight_identity h0 h1 h2 hsurface (sector i)
  simpa [Finset.prod_mul_distrib] using hprod


theorem triHexFK_globalSweepSum_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (external : (ι → ThreeTerminalConnectivity) → Real) :
    (y0 * y1 * y2) ^ Fintype.card ι *
        starFKGlobalSweepSum q y0Star y1Star y2Star external =
      (q ^ 2) ^ Fintype.card ι *
        triangleFKGlobalSweepSum y0 y1 y2 external := by
  unfold starFKGlobalSweepSum triangleFKGlobalSweepSum
  rw [mul_sum, mul_sum]
  apply Finset.sum_congr rfl
  intro sector _
  calc
    (y0 * y1 * y2) ^ Fintype.card ι *
        (external sector *
          ∏ i, starFKTerminalWeight q y0Star y1Star y2Star (sector i)) =
      external sector *
        ((y0 * y1 * y2) ^ Fintype.card ι *
          ∏ i, starFKTerminalWeight q y0Star y1Star y2Star (sector i)) := by
        ring
    _ = external sector *
        ((q ^ 2) ^ Fintype.card ι *
          ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i)) := by
        rw [triHexFK_globalSweep_sector_identity h0 h1 h2 hsurface sector]
    _ = (q ^ 2) ^ Fintype.card ι *
        (external sector *
          ∏ i, triangleFKTerminalWeight y0 y1 y2 (sector i)) := by
        ring


theorem triHexFK_globalSweepRatio_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (external observable : (ι → ThreeTerminalConnectivity) → Real) :
    starFKGlobalSweepRatio q y0Star y1Star y2Star external observable =
      triangleFKGlobalSweepRatio y0 y1 y2 external observable := by
  have hscale :
      (q ^ 2) ^ Fintype.card ι /
          (y0 * y1 * y2) ^ Fintype.card ι ≠ 0 :=
    div_ne_zero (pow_ne_zero _ (pow_ne_zero 2 hq))
      (pow_ne_zero _ hyprod)
  have scale (coeff : (ι → ThreeTerminalConnectivity) → Real) :
      starFKGlobalSweepSum q y0Star y1Star y2Star coeff =
        ((q ^ 2) ^ Fintype.card ι /
          (y0 * y1 * y2) ^ Fintype.card ι) *
            triangleFKGlobalSweepSum y0 y1 y2 coeff := by
    have hid := triHexFK_globalSweepSum_identity
      (ι := ι) h0 h1 h2 hsurface coeff
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (pow_ne_zero _ hyprod)).2
    calc
      starFKGlobalSweepSum q y0Star y1Star y2Star coeff *
          (y0 * y1 * y2) ^ Fintype.card ι =
        (y0 * y1 * y2) ^ Fintype.card ι *
          starFKGlobalSweepSum q y0Star y1Star y2Star coeff := by ring
      _ = (q ^ 2) ^ Fintype.card ι *
          triangleFKGlobalSweepSum y0 y1 y2 coeff := hid
  unfold starFKGlobalSweepRatio triangleFKGlobalSweepRatio
  rw [scale (fun sector => external sector * observable sector), scale external]
  exact mul_div_mul_left _ _ hscale


end StatMech.FK.PeriodicPlanar

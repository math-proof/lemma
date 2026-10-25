/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKFiniteWiredSweep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKGlobalSweep.Part5
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part18
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredSweep
open Finset


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

noncomputable section

theorem triHexFK_finiteWiredBoundaryReachRatio_eq
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    {q y0 y1 y2 y0Star y1Star y2Star : Real}
    (hq : q ≠ 0) (hyprod : y0 * y1 * y2 ≠ 0)
    (h0 : y0 * y0Star = q) (h1 : y1 * y1Star = q)
    (h2 : y2 * y2Star = q)
    (hsurface : FrontierA.triangularFKCriticalSurface q y0 y1 y2 = 0)
    (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary] (root : V) :
    starFKFiniteWiredBoundaryReachRatio q y0Star y1Star y2Star
        terminal boundary root =
      triangleFKFiniteWiredBoundaryReachRatio q y0 y1 y2
        terminal boundary root := by
  unfold starFKFiniteWiredBoundaryReachRatio
    triangleFKFiniteWiredBoundaryReachRatio
  rw [starFKGlobalConfigSum_eq_sweepSum,
    starFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum,
    triangleFKGlobalConfigSum_eq_sweepSum]
  exact triHexFK_globalSweepRatio_eq hq hyprod h0 h1 h2 hsurface
    (triHexFKTerminalWiredExternal q terminal boundary)
    (triHexFKTerminalBoundaryReachObservable terminal boundary root)


theorem triHexFK_finiteWiredBoundaryReachRatio_eq_homogeneous
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V]
    {q p : Real} (hq : 0 < q) (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0)
    (terminal : ι → Fin 3 → V) (boundary : V → Prop)
    [DecidablePred boundary] (root : V) :
    starFKFiniteWiredBoundaryReachRatio q
        (FrontierA.fkEdgeOdds (BeffaraDC.dualParam p q))
        (FrontierA.fkEdgeOdds (BeffaraDC.dualParam p q))
        (FrontierA.fkEdgeOdds (BeffaraDC.dualParam p q))
        terminal boundary root =
      triangleFKFiniteWiredBoundaryReachRatio q
        (FrontierA.fkEdgeOdds p) (FrontierA.fkEdgeOdds p)
        (FrontierA.fkEdgeOdds p) terminal boundary root := by
  have hy : 0 < FrontierA.fkEdgeOdds p :=
    div_pos hp.1 (sub_pos.mpr hp.2)
  have hdual := FrontierA.fkEdgeOdds_mul_dualParam hp.1 hp.2 hq
  apply triHexFK_finiteWiredBoundaryReachRatio_eq hq.ne'
    (mul_ne_zero (mul_ne_zero hy.ne' hy.ne') hy.ne')
    hdual hdual hdual
  rwa [FrontierA.triangularFKCriticalSurface_diagonal]


end
end StatMech.FK.PeriodicPlanar

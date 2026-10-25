/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearHomotopyReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngleHomotopy.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearHomotopyReduction


namespace StatMech.FrontierA

open scoped BigOperators

open Set

open StatMech.Onsager.BaseCase

structure KWRectilinearPhaseHomotopy
    {n m : ℕ} [NeZero n] [NeZero m]
    (source : KWFiniteSimplePolygon n) where
  polygon : ℝ → KWFiniteSimplePolygon m
  vertex_continuous : ∀ k : Fin m,
    ContinuousOn (fun t ↦ (polygon t).vertex k) (Icc 0 1)
  turn_ne_pi : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k : Fin m,
    (Complex.arg ((polygon t).edgeVector (k + 1)) : Real.Angle) -
        (Complex.arg ((polygon t).edgeVector k) : Real.Angle) ≠
      (Real.pi : Real.Angle)
  source_phase : kwVectorPhaseCycle source.edgeList =
    ∏ k : Fin m, kwVectorTurnPhase
      ((polygon 0).edgeVector k) ((polygon 0).edgeVector (k + 1))
  direction : Fin m → Fin 4
  direction_closed : ∑ k, stepOf (direction k) = 0
  direction_simple : Function.Injective (pos direction)
  direction_three_le : 3 ≤ m
  direction_nonbacktracking : ∀ k, direction (k + 1) ≠ direction k + 2
  target_scale : Fin m → ℝ
  target_scale_pos : ∀ k, 0 < target_scale k
  target_edge : ∀ k,
    (polygon 1).edgeVector k =
      target_scale k * kwRectilinearVector (direction k)


end StatMech.FrontierA

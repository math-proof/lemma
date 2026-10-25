/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearHomotopyReduction.Part2
import Mathlib.Topology.MetricSpace.HausdorffDistance


namespace StatMech.FrontierA

open scoped Convex Pointwise

open scoped NNReal ENNReal

open Set


def KWFiniteSimplePolygon.closedEdge
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (i : Fin n) : Set ℂ :=
  segment ℝ (polygon.vertex i) (polygon.vertex (i + 1))


def KWEdgesNonincident {n : ℕ} [NeZero n] (i j : Fin n) : Prop :=
  i ≠ j ∧ i ≠ j + 1 ∧ i + 1 ≠ j

end StatMech.FrontierA

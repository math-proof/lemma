module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearHomotopyReduction.Part2
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearSeparation


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearSeparation.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open scoped Convex Pointwise

open scoped NNReal ENNReal

open Set


def KWFiniteSimplePolygon.closedEdgeTube
    {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n)
    (r : NNReal) (i : Fin n) : Set ℂ :=
  {z | ∃ x ∈ polygon.closedEdge i, dist z x < r}

end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualIncidentSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveSameEdgeMiddle.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealLocalSeparation
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveActualIncidentSeparation


namespace StatMech.FrontierA

open scoped NNReal

open Set

def KWAdaptivePatchedData.outgoingRetainedCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) : Set ℂ :=
  segment ℝ (patch.outgoingPort i) (polygon.vertex (i + 1))


def KWAdaptivePatchedData.incomingRetainedCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) : Set ℂ :=
  segment ℝ (polygon.vertex i) (patch.incomingPort i)

end StatMech.FrontierA

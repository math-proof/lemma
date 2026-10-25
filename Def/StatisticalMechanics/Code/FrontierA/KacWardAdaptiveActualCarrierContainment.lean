/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveActualCarrierContainment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveActualIncidentSeparation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealApproximation


namespace StatMech.FrontierA

open scoped NNReal

open Set

def KWAdaptivePatchedData.outgoingParameterCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) : Set ℂ :=
  AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) ''
    Icc patch.beta 1

def KWAdaptivePatchedData.incomingParameterCarrier
    {n M : ℕ} [NeZero n] [NeZero M] {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon) (i : Fin n) : Set ℂ :=
  AffineMap.lineMap (polygon.vertex i) (polygon.vertex (i + 1)) ''
    Icc 0 (1 - patch.alpha (i + 1))

end StatMech.FrontierA

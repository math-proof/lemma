/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPolygonJordanEquivalence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordEndpointOrderFour
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonPhaseInduction


namespace StatMech.FrontierA

def KWFiniteSimplePolygonPhaseSign : Prop :=
  ∀ {n : ℕ} [NeZero n] (polygon : KWFiniteSimplePolygon n),
    kwVectorPhaseCycle polygon.edgeList = -1


end StatMech.FrontierA

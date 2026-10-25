/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularSplitSpinor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPrincipalAngleMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor.Part2


namespace StatMech.FrontierA

open SimpleGraph

open scoped BigOperators


noncomputable def kwAngularSplitSpinorPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) :=
  kwPhaseGauge (kwAngularSplitSpinorGauge embedding)
    (kwAngularSplitPhase embedding)

end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Mathlib.Analysis.Convex.StrictConvexSpace


namespace StatMech.FrontierA

open Set SimpleGraph

open scoped NNReal ENNReal


def KWStraightLineEmbedding.dartClosedEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) : Set ℂ :=
  segment ℝ (embedding.vertex d.fst) (embedding.vertex d.snd)

end StatMech.FrontierA

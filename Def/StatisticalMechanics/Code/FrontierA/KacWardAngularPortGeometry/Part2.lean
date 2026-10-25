/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Mathlib.Analysis.Convex.StrictConvexSpace
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortGeometry.Part2


namespace StatMech.FrontierA

open Set SimpleGraph

open scoped NNReal ENNReal


noncomputable def KWStraightLineEmbedding.dartUnit
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (d : G.Dart) : ℂ :=
  (embedding.vertex d.snd - embedding.vertex d.fst) /
    ‖embedding.vertex d.snd - embedding.vertex d.fst‖


noncomputable def kwAngularPortVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (r : ℝ) (p : KWDartPort G) : ℂ :=
  embedding.vertex p.1 +
    (r : ℂ) * embedding.dartUnit (kwDartOfPort G p)

end StatMech.FrontierA

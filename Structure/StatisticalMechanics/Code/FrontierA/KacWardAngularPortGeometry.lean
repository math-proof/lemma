/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAngularPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Mathlib.Analysis.Convex.StrictConvexSpace
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularPortGeometry


namespace StatMech.FrontierA

open Set SimpleGraph

open scoped NNReal ENNReal


structure KWAngularPortRadiusData
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) where
  radius : NNReal
  radius_pos : 0 < radius
  vertex_separated : ∀ v w : V, v ≠ w →
    4 * (radius : ℝ) < dist (embedding.vertex v) (embedding.vertex w)
  edge_long : ∀ d : G.Dart,
    4 * (radius : ℝ) <
      ‖embedding.vertex d.snd - embedding.vertex d.fst‖
  vertex_edge_separated : ∀ (v : V) (d : G.Dart),
    v ≠ d.fst → v ≠ d.snd →
      ∀ y ∈ embedding.dartClosedEdge d,
        2 * (radius : ℝ) < dist (embedding.vertex v) y

end StatMech.FrontierA

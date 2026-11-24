module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPrincipalCancellation
public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Def.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding
open scoped BigOperators Affine EuclideanGeometry Real
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

theorem KWStraightLineEmbedding.dartVector_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart : G.Dart) :
    embedding.vertex dart.snd - embedding.vertex dart.fst ≠ 0 := by
  rw [sub_ne_zero]
  exact embedding.vertex_injective.ne dart.snd_ne_fst


end StatMech.FrontierA

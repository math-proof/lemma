module
public import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPrincipalCancellation
public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
public import Structure.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding
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

noncomputable def KWStraightLineEmbedding.dartAngle
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart : G.Dart) : Real.Angle :=
  (Complex.arg (embedding.vertex dart.snd - embedding.vertex dart.fst) : ℝ)

end StatMech.FrontierA

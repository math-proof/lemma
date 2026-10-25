/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStraightLineEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPrincipalCancellation
import Mathlib.Analysis.Complex.Arg
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding
open scoped BigOperators Affine EuclideanGeometry Real
open Finset SimpleGraph


namespace StatMech.FrontierA

noncomputable def KWStraightLineEmbedding.turnPhase
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G) (dart next : G.Dart) : ℂ :=
  Complex.exp
    (((Complex.arg
      ((embedding.vertex next.snd - embedding.vertex next.fst) /
        (embedding.vertex dart.snd - embedding.vertex dart.fst)) : ℂ) *
          Complex.I) / 2)


end StatMech.FrontierA

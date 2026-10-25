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
open scoped BigOperators Affine EuclideanGeometry Real
open Finset SimpleGraph


namespace StatMech.FrontierA

structure KWStraightLineEmbedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  vertex : V → ℂ
  vertex_injective : Function.Injective vertex
  vertex_not_strictly_between : ∀ (dart : G.Dart) (v : V),
    v ≠ dart.fst → v ≠ dart.snd →
      ¬Sbtw ℝ (vertex dart.fst) (vertex v) (vertex dart.snd)
  edgeInteriors_disjoint : ∀ (dart next : G.Dart),
    dart.edge ≠ next.edge →
      Disjoint
        {z : ℂ | Sbtw ℝ (vertex dart.fst) z (vertex dart.snd)}
        {z : ℂ | Sbtw ℝ (vertex next.fst) z (vertex next.snd)}


end StatMech.FrontierA

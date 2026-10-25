/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FKTutte.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
open scoped BigOperators
open SimpleGraph


namespace StatMech.FK

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def spanningClusterCount (A : Finset (Sym2 V)) : ℕ :=
  Nat.card (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).ConnectedComponent


noncomputable def tutteEval (G : SimpleGraph V) [DecidableRel G.Adj] (x y : ℝ) : ℝ :=
  ∑ A ∈ G.edgeFinset.powerset,
    (x - 1) ^ (spanningClusterCount A - Nat.card G.ConnectedComponent) *
      (y - 1) ^ (A.card + spanningClusterCount A - Fintype.card V)


noncomputable def randomClusterPartition (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : ℝ) : ℝ :=
  ∑ A ∈ G.edgeFinset.powerset,
    p ^ A.card * (1 - p) ^ (G.edgeFinset.card - A.card) *
      q ^ spanningClusterCount A


def edgeSetConfig (A : Finset (Sym2 V)) : ConfigSpace (Sym2 V) :=
  fun e => decide (e ∈ A)

end StatMech.FK

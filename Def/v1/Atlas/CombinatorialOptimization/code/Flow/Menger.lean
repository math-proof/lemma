module
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowMinCut.Part2
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.MaxFlowMinCut
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.MaxFlowAugPath
public import Theorem.Finset.Atlas.v1.CombinatorialOptimization.code.Flow.FlowDecomposition
public import Instance.v1.Atlas.CombinatorialOptimization.code.Flow.MaxFlowAugPath
public import Def.v1.Atlas.CombinatorialOptimization.code.Flow.FlowDecomposition.Part3
public import Structure.v1.Atlas.CombinatorialOptimization.code.Flow.Menger.Part2
open Finset BigOperators Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Flow/Menger.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace NetworkFlow

variable {V : Type*} [Fintype V] [DecidableEq V]

def DirPath.edges {G : DirectedGraph V} (p : DirPath G) : List (V × V) :=
  p.vertices.zip p.vertices.tail

def PairwiseEdgeDisjoint {G : DirectedGraph V} (paths : Fin k → DirPath G) : Prop :=
  ∀ i j : Fin k, i ≠ j →
    ∀ e : V × V, ¬ (e ∈ (paths i).edges ∧ e ∈ (paths j).edges)

end NetworkFlow
end

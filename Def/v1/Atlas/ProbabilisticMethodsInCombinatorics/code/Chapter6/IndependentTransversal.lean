/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/IndependentTransversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.Basic

@[expose] public section

set_option maxHeartbeats 400000

open SimpleGraph Finset


namespace IndependentTransversal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A function `f : Fin r → V` is an *independent transversal* for the partition
`parts : Fin r → Finset V` of $V$ in the graph $G$ if it picks one vertex from each part
($f i \in $ `parts i`) and its image is an independent set in $G$. -/
def IsIndependentTransversal (G : SimpleGraph V) (parts : Fin r → Finset V)
    (f : Fin r → V) : Prop :=
  (∀ i, f i ∈ parts i) ∧ G.IsIndepSet (Set.range f)

end IndependentTransversal

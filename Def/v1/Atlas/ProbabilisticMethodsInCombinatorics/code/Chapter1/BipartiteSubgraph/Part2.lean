/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.BipartiteSubgraph.Part2
open Finset BigOperators SimpleGraph


namespace BipartiteSubgraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `flipAt v f` is the Boolean labelling obtained from `f` by negating its value at `v`. -/
def flipAt {V : Type*} [DecidableEq V] (v : V) (f : V → Bool) : V → Bool :=
  Function.update f v (!f v)

/-- The cut subgraph of `G` induced by a Boolean labelling `f`: the subgraph consisting
of edges `{u, v}` of `G` with `f u ≠ f v`. -/
def cutGraph {V : Type*} (G : SimpleGraph V) (f : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ f u ≠ f v
  symm _ _ := fun ⟨h1, h2⟩ => ⟨G.symm h1, Ne.symm h2⟩
  loopless := ⟨fun _ h => absurd rfl h.2⟩

end BipartiteSubgraph

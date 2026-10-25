/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.BipartiteSubgraph
open Finset BigOperators SimpleGraph


namespace BipartiteSubgraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For a Boolean labelling `f : V → Bool`, `boolCut f e` returns `true` when the
unordered pair `e = s(u, v)` is a cut edge, i.e. `f u ≠ f v`. -/
def boolCut (f : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun u v => f u != f v, bne_symm f⟩

end BipartiteSubgraph

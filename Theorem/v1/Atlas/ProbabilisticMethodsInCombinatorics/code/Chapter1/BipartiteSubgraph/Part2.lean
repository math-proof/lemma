/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.BipartiteSubgraph
open Finset BigOperators SimpleGraph


namespace BipartiteSubgraph

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- Evaluation of `boolCut` on an explicit pair `s(u, v)`. -/
@[simp] lemma boolCut_mk (f : V → Bool) (u v : V) :
    boolCut f s(u, v) = (f u != f v) :=
  Sym2.lift_mk _ u v

end BipartiteSubgraph

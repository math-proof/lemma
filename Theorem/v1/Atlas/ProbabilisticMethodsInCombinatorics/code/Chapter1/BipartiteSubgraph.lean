/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset BigOperators SimpleGraph


namespace BipartiteSubgraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Boolean inequality `!=` is symmetric: $(f(a) \neq f(b)) = (f(b) \neq f(a))$. -/
lemma bne_symm {V : Type*} (f : V → Bool) (a b : V) :
    (f a != f b) = (f b != f a) := by
  rcases Bool.eq_false_or_eq_true (f a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (f b) with hb | hb <;> simp [ha, hb]

end BipartiteSubgraph

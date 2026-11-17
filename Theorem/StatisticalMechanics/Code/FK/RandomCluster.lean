/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Def.StatisticalMechanics.Code.FK.RandomCluster
open scoped BigOperators

public section

namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem openSub_adj (ω : ConfigSpace (Sym2 V)) (x y : V) :
    (openSub G ω).Adj x y ↔ G.Adj x y ∧ ω s(x, y) = true :=
  Iff.rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in


theorem openSub_le (ω : ConfigSpace (Sym2 V)) : openSub G ω ≤ G := fun _ _ h => h.1


end FK
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


def openSub (ω : ConfigSpace (Sym2 V)) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ ω s(x, y) = true
  symm := by
    constructor
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    rw [Sym2.eq_swap]; exact h.2
  loopless := ⟨fun x h => h.1.ne rfl⟩

end FK
end StatMech

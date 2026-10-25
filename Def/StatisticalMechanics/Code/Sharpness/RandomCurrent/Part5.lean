/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/RandomCurrent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part5
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech

namespace Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def oddSubgraph (n : Current V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ Odd (n s(x, y))
  symm := by
    constructor
    intro x y ⟨hadj, hodd⟩
    exact ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun x ⟨hadj, _⟩ => hadj.ne rfl⟩

end Sharpness
end StatMech

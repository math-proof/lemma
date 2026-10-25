/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCutInjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCut
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

variable {V P : Type*} [Fintype V] [DecidableEq V]
  [Fintype P] [DecidableEq P]


def ons_multibondSupportGraph (ends : P → V × V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ edge : P,
    ends edge = (x, y) ∨ ends edge = (y, x)
  symm := by
    constructor
    rintro x y ⟨hne, edge, h | h⟩
    · exact ⟨hne.symm, edge, Or.inr h⟩
    · exact ⟨hne.symm, edge, Or.inl h⟩
  loopless := ⟨fun x h => h.1 rfl⟩

end
end StatMech.Onsager

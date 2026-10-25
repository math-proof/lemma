/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open scoped BigOperators


namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


def monoIndicator {q : ℕ} (σ : V → Fin q) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun x y => if σ x = σ y then (1 : ℝ) else 0, by
    intro a b
    dsimp only
    by_cases h : σ a = σ b
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun he : σ b = σ a => h he.symm)]⟩

end Potts
end StatMech

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Potts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FK.Potts
open scoped BigOperators


namespace StatMech

namespace Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] in
@[simp]
theorem monoIndicator_mk {q : ℕ} (σ : V → Fin q) (x y : V) :
    monoIndicator σ (s(x, y)) = if σ x = σ y then (1 : ℝ) else 0 :=
  Sym2.lift_mk _ _ _

omit [Fintype V] [DecidableEq V] in
theorem monoIndicator_nonneg {q : ℕ} (σ : V → Fin q) (e : Sym2 V) :
    0 ≤ monoIndicator σ e := by
  induction e with
  | _ x y => rw [monoIndicator_mk]; split <;> norm_num


end Potts
end StatMech

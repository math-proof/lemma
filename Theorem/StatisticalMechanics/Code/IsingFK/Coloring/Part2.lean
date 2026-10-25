/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Coloring.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.IsingFK.Coloring.Part2
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp]
theorem monoBool_mk {q : ℕ} (σ : V → Fin q) (x y : V) :
    monoBool σ s(x, y) = decide (σ x = σ y) := by
  unfold monoBool; rw [Sym2.lift_mk]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem monoBool_iff {q : ℕ} (σ : V → Fin q) (x y : V) :
    monoBool σ s(x, y) = true ↔ σ x = σ y := by
  rw [monoBool_mk, decide_eq_true_eq]


end IsingFK
end StatMech

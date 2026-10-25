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
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring
open scoped BigOperators


namespace StatMech

namespace IsingFK

open StatMech.FK StatMech.Potts

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


def monoBool {q : ℕ} (σ : V → Fin q) : Sym2 V → Bool :=
  Sym2.lift ⟨fun x y => decide (σ x = σ y), by
    intro a b
    simp only [decide_eq_decide]
    exact ⟨Eq.symm, Eq.symm⟩⟩

end IsingFK
end StatMech

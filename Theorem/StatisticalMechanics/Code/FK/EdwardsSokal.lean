/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdwardsSokal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.Potts.Part6
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.EdwardsSokal
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


omit [DecidableEq V] in


theorem esWeight_nonneg {q : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (σ : V → Fin q) (ω : ConfigSpace (Sym2 V)) : 0 ≤ esWeight G p σ ω := by
  unfold esWeight esEdgeFactor
  apply Finset.prod_nonneg
  intro e _
  split
  · exact mul_nonneg hp (Potts.monoIndicator_nonneg σ e)
  · linarith


end FK
end StatMech

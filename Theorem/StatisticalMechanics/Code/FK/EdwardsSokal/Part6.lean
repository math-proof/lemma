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
import Def.StatisticalMechanics.Code.FK.EdwardsSokal.Part6
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem esZ_eq_fkZ (q : ℕ) (p : ℝ) : esZ G q p = fkZ G p (q : ℝ) := by
  unfold esZ fkZ
  exact Finset.sum_congr rfl fun ω _ => esWeight_sum G p ω


theorem esZ_eq_pottsZ (q : ℕ) [NeZero q] (β J : ℝ) :
    esZ G q (1 - Real.exp (-(β * J))) = esFirstConst G β J * Potts.pottsZ G q β J := by
  unfold esZ
  rw [Finset.sum_comm]
  unfold Potts.pottsZ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  exact esWeight_sum_eq_pottsWeight G β J σ


theorem esZ_pos {q : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : ℝ)) :
    0 < esZ G q p := by
  rw [esZ_eq_fkZ]
  exact fkZ_pos G hp hp1 hq


end FK
end StatMech

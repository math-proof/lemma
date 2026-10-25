/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.FK.RandomCluster.Part6
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp]
theorem fkPMF_apply {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) :
    fkPMF G hp hp1 hq ω = ENNReal.ofReal (fkProb G p q ω) :=
  PMF.ofFintype_apply _ _


theorem fkWeight_one (p : ℝ) (ω : ConfigSpace (Sym2 V)) :
    fkWeight G p 1 ω = edgeProduct G p ω := by
  unfold fkWeight
  rw [one_pow, mul_one]


theorem fkZ_one (p : ℝ) : fkZ G p 1 = ∑ ω : ConfigSpace (Sym2 V), edgeProduct G p ω := by
  unfold fkZ
  exact Finset.sum_congr rfl fun ω _ => fkWeight_one G p ω

end FK
end StatMech

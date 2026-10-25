/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.FK.RandomCluster.Part5
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fkProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 ≤ fkProb G p q ω :=
  div_nonneg (fkWeight_nonneg G hp hp1 hq ω) (fkZ_pos G hp hp1 hq).le


theorem fkProb_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ω : ConfigSpace (Sym2 V)) : 0 < fkProb G p q ω :=
  div_pos (fkWeight_pos G hp hp1 hq ω) (fkZ_pos G hp hp1 hq)


theorem fkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ω : ConfigSpace (Sym2 V), fkProb G p q ω = 1 := by
  unfold fkProb
  rw [← Finset.sum_div]
  exact div_self (fkZ_ne_zero G hp hp1 hq)


end FK
end StatMech

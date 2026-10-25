/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Def.StatisticalMechanics.Code.FK.DomainMarkov.Part4
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem inducedFkProb_nonneg {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) :
    0 ≤ inducedFkProb G p q F ψ ω :=
  div_nonneg (fkWeight_nonneg G hp hp1 hq ω) (inducedFkZ_pos G hp hp1 hq F ψ).le


theorem inducedFkProb_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ ω : ConfigSpace (Sym2 V)) :
    0 < inducedFkProb G p q F ψ ω :=
  div_pos (fkWeight_pos G hp hp1 hq ω) (inducedFkZ_pos G hp hp1 hq F ψ)


theorem inducedFkProb_sum_eq_one {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    ∑ ω ∈ condFibre F ψ, inducedFkProb G p q F ψ ω = 1 := by
  unfold inducedFkProb
  rw [← Finset.sum_div]
  exact div_self (inducedFkZ_ne_zero G hp hp1 hq F ψ)


end FK
end StatMech

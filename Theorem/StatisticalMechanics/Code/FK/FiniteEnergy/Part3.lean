/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.Comparison
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.FiniteEnergy.Part2
open scoped BigOperators
open Module SimpleGraph


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem condOpen_eq_weightRatio {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    condOpen G p q e ω = fkWeight G p q (setOpen e ω) /
      (fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω)) := by
  unfold condOpen fkProb
  rw [← add_div]
  exact div_div_div_cancel_right₀ (fkZ_ne_zero G hp hp1 hq) _ _


theorem condOpen_eq_half {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    {e : Sym2 V} (he : e ∉ G.edgeFinset) (ω : ConfigSpace (Sym2 V)) :
    condOpen G p q e ω = 1 / 2 := by
  rw [condOpen_eq_weightRatio G hp hp1 hq]
  have hep : edgeProduct G p (setOpen e ω) = edgeProduct G p (setClosed e ω) := by
    unfold edgeProduct
    apply Finset.prod_congr rfl
    intro e' he'
    have hne : e' ≠ e := fun h => he (h ▸ he')
    rw [setOpen_of_ne hne, setClosed_of_ne hne]
  have hk : numClusters G (setOpen e ω) = numClusters G (setClosed e ω) :=
    numClusters_congr_openSub G (openSub_setOpen_eq_setClosed_of_notMem G he ω)
  have hweq : fkWeight G p q (setOpen e ω) = fkWeight G p q (setClosed e ω) := by
    unfold fkWeight; rw [hep, hk]
  rw [hweq]
  have hpos := fkWeight_pos G hp hp1 hq (setClosed e ω)
  rw [← two_mul, div_eq_div_iff (by positivity) (by norm_num)]
  ring


end FK
end StatMech

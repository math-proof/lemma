/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CircuitLowerBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem fkWeight_setClosed_ge {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (e : Sym2 V) (ω : ConfigSpace (Sym2 V)) :
    cFE p q * (fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω))
      ≤ fkWeight G p q (setClosed e ω) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  by_cases he : e ∈ G.edgeFinset
  · have hW1pos : 0 < fkWeight G p q (setOpen e ω) := fkWeight_pos G hp hp1 hq0 _
    have hW0pos : 0 < fkWeight G p q (setClosed e ω) := fkWeight_pos G hp hp1 hq0 _
    have hlo : (1 - p) * fkWeight G p q (setOpen e ω) ≤ p * fkWeight G p q (setClosed e ω) :=
      fkWeight_lo G hp hp1 hq he ω
    
    have hcfe : cFE p q ≤ 1 - p := min_le_right _ _
    have hkey : (1 - p) * (fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω))
        ≤ fkWeight G p q (setClosed e ω) := by nlinarith
    have hsum : (0 : ℝ) ≤ fkWeight G p q (setOpen e ω) + fkWeight G p q (setClosed e ω) := by
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcfe hsum]
  · 
    
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
    have hcfe : cFE p q ≤ 1 / 2 := cFE_le_half hp hp1 hq
    have hW0pos : 0 < fkWeight G p q (setClosed e ω) := fkWeight_pos G hp hp1 hq0 _
    rw [hweq]
    nlinarith [mul_le_mul_of_nonneg_right hcfe
      (by linarith : (0 : ℝ) ≤ fkWeight G p q (setClosed e ω) + fkWeight G p q (setClosed e ω))]


end FK
end StatMech

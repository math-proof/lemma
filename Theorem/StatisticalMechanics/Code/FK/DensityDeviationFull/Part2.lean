/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityDeviationFull.lean -/

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
import Theorem.StatisticalMechanics.Code.FK.DensityBounds
import Theorem.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.FK.DensityDeviationFull.Part2
open scoped BigOperators


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem den_openCount_upper_deviation {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε ≤ 1 - p)
    (hEpos : 0 < (G.edgeFinset.card : ℝ)) :
    ε ≤ fkOpenCountLeProb G p q ((p + ε) * (G.edgeFinset.card : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  have hpe1 : p + ε ≤ 1 := by linarith
  have hrm := reverse_markov_upper
      (fun ω : ConfigSpace (Sym2 V) => fkProb G p q ω)
      (fun ω => (chOpenCount G ω : ℝ))
      (fun ω => fkProb_nonneg G hp hp1 hq0 ω)
      (fkProb_sum_eq_one G hp hp1 hq0)
      (fun ω => by positivity)
      (M := (G.edgeFinset.card : ℝ)) (μ := p) (ε := ε)
      (fkMeanOpenCount_le G hp hp1 hq) hp.le hε hEpos
  
  have hε_le : ε ≤ ε / (p + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < p + ε)]
    nlinarith
  exact le_trans hε_le hrm


theorem den_openCount_lower_deviation {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ p / (p + q * (1 - p)))
    (hEpos : 0 < (G.edgeFinset.card : ℝ)) :
    ε ≤ fkOpenCountGeProb G p q
        ((p / (p + q * (1 - p)) - ε) * (G.edgeFinset.card : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set b := p / (p + q * (1 - p)) with hb
  have hden : 0 < p + q * (1 - p) := by nlinarith
  
  have hb_pos : 0 < b := by rw [hb]; positivity
  have hb_le_one : b ≤ 1 := by
    rw [hb, div_le_one hden]; nlinarith
  have hrm := reverse_markov_lower
      (fun ω : ConfigSpace (Sym2 V) => fkProb G p q ω)
      (fun ω => (chOpenCount G ω : ℝ))
      (M := (G.edgeFinset.card : ℝ))
      (fun ω => fkProb_nonneg G hp hp1 hq0 ω)
      (fkProb_sum_eq_one G hp hp1 hq0)
      (fun ω => by
        show (chOpenCount G ω : ℝ) ≤ (G.edgeFinset.card : ℝ)
        unfold chOpenCount; exact_mod_cast Finset.card_filter_le _ _)
      (ν := b) (ε := ε)
      (fkMeanOpenCount_ge G hp hp1 hq) hb_le_one hε hEpos
  
  have hε_le : ε ≤ ε / (1 - b + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - b + ε)]
    nlinarith
  exact le_trans hε_le hrm

end FK
end StatMech

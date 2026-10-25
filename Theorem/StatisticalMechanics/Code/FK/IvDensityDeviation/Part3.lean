/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IvDensityDeviation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.DensityDeviationFull.Part2
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.AvgDensityCollapse
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Def.StatisticalMechanics.Code.FK.IvDensityDeviation.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem ivd_freeAvgDensity_nonneg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    0 ≤ ivd_freeAvgDensity d n p := by
  unfold ivd_freeAvgDensity
  exact div_nonneg (Finset.sum_nonneg fun e _ => ivd_freeEdgeDensity_nonneg n e hp hp1)
    (by positivity)


theorem ivd_freeAvgDensity_le_one (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ivd_freeAvgDensity d n p ≤ 1 := by
  unfold ivd_freeAvgDensity
  rw [div_le_one hEpos]
  calc ∑ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p
      ≤ ∑ _e ∈ (boxGraph d n).edgeFinset, (1:ℝ) :=
        Finset.sum_le_sum fun e _ => ivd_freeEdgeDensity_le_one n e hp hp1
    _ = ((boxGraph d n).edgeFinset.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]


theorem ivd_wiredAvgDensity_le_one (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ivd_wiredAvgDensity d n p ≤ 1 := by
  unfold ivd_wiredAvgDensity
  rw [div_le_one hEpos]
  calc ∑ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p
      ≤ ∑ _e ∈ (boxGraph d n).edgeFinset, (1:ℝ) :=
        Finset.sum_le_sum fun e _ => ivd_wiredEdgeDensity_le_one n e hp hp1
    _ = ((boxGraph d n).edgeFinset.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]


theorem ivd_freeMeanOpenCount_le_avg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    fkMeanOpenCount (boxGraph d n) p 2
      ≤ ivd_freeAvgDensity d n p * ((boxGraph d n).edgeFinset.card : ℝ) := by
  unfold ivd_freeAvgDensity
  rw [div_mul_cancel₀ _ (ne_of_gt hEpos), fkMeanOpenCount_eq_sum_marginals]
  refine Finset.sum_le_sum fun e he => ?_
  rw [(edgeMargProb_fkProb (boxGraph d n) p 2 e).symm]
  have h1 := dfi_free_per_edge_le n n (le_refl n) e hp hp1
  rwa [ivd_innerEdgeLE_refl n e] at h1


theorem ivd_wiredMeanOpenCount_ge_avg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ivd_wiredAvgDensity d n p * ((boxGraph d n).edgeFinset.card : ℝ)
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (chOpenCount (boxGraph d n) ω : ℝ)
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  unfold ivd_wiredAvgDensity
  rw [div_mul_cancel₀ _ (ne_of_gt hEpos), ivd_wiredMeanOpenCount_eq_sum_marginals]
  refine Finset.sum_le_sum fun e he => ?_
  have h1 := dfi_wired_per_edge_ge n n (le_refl n) e hp hp1
  rwa [ivd_innerEdgeLE_refl n e] at h1


theorem den_openCount_upper_deviation_iv_avg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε ≤ 1 - ivd_freeAvgDensity d n p)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ε ≤ fkOpenCountLeProb (boxGraph d n) p 2
        ((ivd_freeAvgDensity d n p + ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
  set a := ivd_freeAvgDensity d n p with ha
  have ha0 : 0 ≤ a := ivd_freeAvgDensity_nonneg n hp hp1
  have hae1 : a + ε ≤ 1 := by linarith
  have hrm := reverse_markov_upper
      (fun ω : ConfigSpace (Sym2 (boxVerts d n)) => fkProb (boxGraph d n) p 2 ω)
      (fun ω => (chOpenCount (boxGraph d n) ω : ℝ))
      (fun ω => fkProb_nonneg (boxGraph d n) hp hp1 (by norm_num) ω)
      (fkProb_sum_eq_one (boxGraph d n) hp hp1 (by norm_num))
      (fun ω => by positivity)
      (M := ((boxGraph d n).edgeFinset.card : ℝ)) (μ := a) (ε := ε)
      (ivd_freeMeanOpenCount_le_avg n hp hp1 hEpos) ha0 hε hEpos
  have hε_le : ε ≤ ε / (a + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < a + ε)]; nlinarith
  exact le_trans hε_le hrm


theorem den_openCount_lower_deviation_iv_avg (n : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ ivd_wiredAvgDensity d n p)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ε ≤ ivd_wiredOpenCountGeProb d n p
        ((ivd_wiredAvgDensity d n p - ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
  set b := ivd_wiredAvgDensity d n p with hb
  have hb1 : b ≤ 1 := ivd_wiredAvgDensity_le_one n hp hp1 hEpos
  have hrm := reverse_markov_lower
      (fun ω : ConfigSpace (Sym2 (boxVerts d n)) =>
        wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω)
      (fun ω => (chOpenCount (boxGraph d n) ω : ℝ))
      (M := ((boxGraph d n).edgeFinset.card : ℝ))
      (fun ω => wiredFkProb_nonneg (boxGraph d n) (boxBoundary d n) hp hp1 (by norm_num) ω)
      (wiredFkProb_sum_eq_one (boxGraph d n) (boxBoundary d n) hp hp1 (by norm_num))
      (fun ω => by
        change (chOpenCount (boxGraph d n) ω : ℝ) ≤ ((boxGraph d n).edgeFinset.card : ℝ)
        unfold chOpenCount; exact_mod_cast Finset.card_filter_le _ _)
      (ν := b) (ε := ε)
      (ivd_wiredMeanOpenCount_ge_avg n hp hp1 hEpos) hb1 hε hEpos
  have hε_le : ε ≤ ε / (1 - b + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - b + ε)]; nlinarith
  exact le_trans hε_le hrm

end FK
end StatMech

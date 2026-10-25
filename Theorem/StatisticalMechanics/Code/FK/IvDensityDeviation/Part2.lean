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
import Def.StatisticalMechanics.Code.FK.IvDensityDeviation
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem den_openCount_upper_deviation_iv (n : ℕ) {p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (ha0 : 0 ≤ a)
    (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, freeEdgeDensity d 2 (edgeIncl d n e) p = a)
    {ε : ℝ} (hε : 0 < ε) (hεa : ε ≤ 1 - a)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ε ≤ fkOpenCountLeProb (boxGraph d n) p 2 ((a + ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
  have hae1 : a + ε ≤ 1 := by linarith
  have hrm := reverse_markov_upper
      (fun ω : ConfigSpace (Sym2 (boxVerts d n)) => fkProb (boxGraph d n) p 2 ω)
      (fun ω => (chOpenCount (boxGraph d n) ω : ℝ))
      (fun ω => fkProb_nonneg (boxGraph d n) hp hp1 (by norm_num) ω)
      (fkProb_sum_eq_one (boxGraph d n) hp hp1 (by norm_num))
      (fun ω => by positivity)
      (M := ((boxGraph d n).edgeFinset.card : ℝ)) (μ := a) (ε := ε)
      (ivd_freeMeanOpenCount_le n hp hp1 hhom) ha0 hε hEpos
  have hε_le : ε ≤ ε / (a + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < a + ε)]
    nlinarith
  exact le_trans hε_le hrm


theorem den_openCount_lower_deviation_iv (n : ℕ) {p b : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hb1 : b ≤ 1)
    (hhom : ∀ e ∈ (boxGraph d n).edgeFinset, wiredEdgeDensity d 2 (edgeIncl d n e) p = b)
    {ε : ℝ} (hε : 0 < ε) (hεb : ε ≤ b)
    (hEpos : 0 < ((boxGraph d n).edgeFinset.card : ℝ)) :
    ε ≤ ivd_wiredOpenCountGeProb d n p ((b - ε) * ((boxGraph d n).edgeFinset.card : ℝ)) := by
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
      (ivd_wiredMeanOpenCount_ge n hp hp1 hhom) hb1 hε hEpos
  have hε_le : ε ≤ ε / (1 - b + ε) := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - b + ε)]
    nlinarith
  exact le_trans hε_le hrm


theorem ivd_freeEdgeDensity_nonneg (n : ℕ) (e : Sym2 (boxVerts d n)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) : 0 ≤ freeEdgeDensity d 2 (edgeIncl d n e) p :=
  ge_of_tendsto (dfi_free_density_eq_limit n e hp hp1)
    (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_nonneg (boxGraph d (n + k)) hp hp1 (by norm_num) _)


theorem ivd_freeEdgeDensity_le_one (n : ℕ) (e : Sym2 (boxVerts d n)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) : freeEdgeDensity d 2 (edgeIncl d n e) p ≤ 1 :=
  le_of_tendsto (dfi_free_density_eq_limit n e hp hp1)
    (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_le_one (boxGraph d (n + k)) hp hp1 (by norm_num) _)


theorem ivd_wiredEdgeDensity_le_one (n : ℕ) (e : Sym2 (boxVerts d n)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1) : wiredEdgeDensity d 2 (edgeIncl d n e) p ≤ 1 :=
  le_of_tendsto (dfi_wired_density_eq_limit n e hp hp1)
    (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (n + k)) (boxBoundary d (n + k))
        hp hp1 (by norm_num) _)


end FK
end StatMech

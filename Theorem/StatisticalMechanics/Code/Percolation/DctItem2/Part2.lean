/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctItem2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.DctSurfacePartition.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Percolation.Sharpness.Part2
import Def.StatisticalMechanics.Code.Percolation.DctItem2
open MeasureTheory Function Set SimpleGraph Filter
open scoped NNReal ENNReal Topology
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem continuousOn_crossProbReal (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    ContinuousOn (crossProbReal d (n + 1)) (Icc a b) := by
  refine ContinuousOn.congr (f := crossPoly d n) ?_ ?_
  · exact (differentiable_boxCrossProb (n + 1)).continuous.continuousOn
  · intro t ht
    exact crossProbReal_eq_prob n (le_trans ha ht.1) (le_trans ht.2 hb)


theorem hasDerivAt_crossProbReal (n : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt (crossProbReal d (n + 1)) (deriv (crossPoly d n) t) t := by
  have hpoly : HasDerivAt (crossPoly d n) (deriv (crossPoly d n) t) t :=
    (differentiable_boxCrossProb (n + 1) t).hasDerivAt
  refine hpoly.congr_of_eventuallyEq ?_
  have hnhds : Ioo (0 : ℝ) 1 ∈ 𝓝 t := Ioo_mem_nhds ht0 ht1
  filter_upwards [hnhds] with s hs
  exact crossProbReal_eq_prob n (le_of_lt hs.1) (le_of_lt hs.2)


theorem phi_ge_one_of_gt_tildePc {p : NNReal} (hp : p ≤ 1) (hgt : tildePc d < p)
    (S : Finset (Site d)) (h0S : origin d ∈ S) : 1 ≤ phi d p hp S := by
  by_contra hlt
  rw [not_le] at hlt
  have hmem : p ∈ tildePcSet d := ⟨hp, S, h0S, hlt⟩
  have hle : p ≤ tildePc d :=
    le_csSup ⟨1, fun q hq => (mem_tildePcSet.mp hq).1⟩ hmem
  exact absurd hle (not_le.mpr hgt)


theorem dct_diffineq_crossProbReal {q : NNReal} (hq1 : (q : ℝ) < 1)
    (htpc0 : 0 < (tildePc d : ℝ)) (n : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (tildePc d : ℝ) (q : ℝ)) :
    deriv (crossPoly d n) t
      ≥ (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t) := by
  obtain ⟨htlo, hthi⟩ := ht
  have ht0 : 0 < t := lt_trans htpc0 htlo
  have ht1 : t < 1 := lt_trans hthi hq1
  set p : NNReal := t.toNNReal with hp_def
  have hp_le1 : p ≤ 1 := Real.toNNReal_le_one.mpr (le_of_lt ht1)
  have hpt : (p : ℝ) = t := Real.coe_toNNReal t (le_of_lt ht0)
  have hp0 : 0 < (p : ℝ) := by rw [hpt]; exact ht0
  have hpr1 : (p : ℝ) < 1 := by rw [hpt]; exact ht1
  
  have hp_gt : tildePc d < p := by
    rw [← NNReal.coe_lt_coe, hpt]; exact htlo
  
  have hm : ∀ S : Finset (Site d), origin d ∈ S → (1 : ℝ) ≤ phi d p hp_le1 S :=
    fun S h0S => phi_ge_one_of_gt_tildePc hp_le1 hp_gt S h0S
  have hdi := dct_differential_inequality p hp_le1 (n + 1) (by omega) hp0 hpr1 1 hm
  
  have hderiv_eq : deriv (crossPoly d n) t
      = deriv (fun q' => prob q' ((boxEdgeFinset d (n + 1)).restrict ''
          (boxCrossingEvent d (n + 1)))) (p : ℝ) := by
    rw [hpt]; rfl
  
  have hcross_eq : boxCrossProb d p hp_le1 (n + 1) = crossProbReal d (n + 1) t := by
    rw [crossProbReal_eq_prob n (le_of_lt ht0) (le_of_lt ht1), boxCrossProb_eq_prob, hpt]
  rw [hderiv_eq, ge_iff_le]
  
  rw [ge_iff_le, hcross_eq] at hdi
  calc (1 / (t * (1 - t))) * (1 - crossProbReal d (n + 1) t)
      = (1 / ((p : ℝ) * (1 - (p : ℝ)))) * 1 * (1 - crossProbReal d (n + 1) t) := by
        rw [hpt]; ring
    _ ≤ deriv (fun q' => prob q' ((boxEdgeFinset d (n + 1)).restrict ''
          (boxCrossingEvent d (n + 1)))) (p : ℝ) := hdi


theorem theta_ge_meanField_unconditional (q : NNReal) (hq : q ≤ 1)
    (htpc0 : 0 < (tildePc d : ℝ)) (hgt : tildePc d < q) (hq1 : (q : ℝ) < 1) :
    theta d q hq ≥ ((q : ℝ) - (tildePc d : ℝ)) / ((q : ℝ) * (1 - (tildePc d : ℝ))) := by
  have haq : (tildePc d : ℝ) < (q : ℝ) := by exact_mod_cast hgt
  exact theta_ge_meanField q hq (tildePc d : ℝ) htpc0 haq hq1
    (fun n t => deriv (crossPoly d n) t)
    (fun n => continuousOn_crossProbReal n (le_of_lt htpc0) (le_of_lt hq1))
    (fun n t ht => hasDerivAt_crossProbReal n (lt_trans htpc0 ht.1) (lt_trans ht.2 hq1))
    (fun n t ht => dct_diffineq_crossProbReal hq1 htpc0 n ht)

end Percolation
end StatMech

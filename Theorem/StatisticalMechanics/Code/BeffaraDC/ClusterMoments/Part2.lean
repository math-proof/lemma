/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ClusterMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TreePercolation.Part6
import Structure.StatisticalMechanics.Code.BeffaraDC.ClusterMoments
open scoped BigOperators
open Set Filter Topology


namespace StatMech

namespace BeffaraDC

namespace ClusterSizeDomination

variable (D : ClusterSizeDomination)


theorem summand_summable (d : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ d * D.dist n) :=
  summable_pow_mul_of_geometricTail D.rate_nonneg D.rate_lt_one D.nonneg D.geometricTail d


theorem allMoments_lt_top (d : ℕ) :
    clusterMoment D.dist d ≤ ∑' n : ℕ, (n : ℝ) ^ d * (D.const * D.rate ^ n) :=
  clusterMoment_le_of_geometricTail D.rate_nonneg D.rate_lt_one D.nonneg D.geometricTail d


theorem moment_nonneg (d : ℕ) : 0 ≤ clusterMoment D.dist d :=
  clusterMoment_nonneg D.nonneg d

end ClusterSizeDomination


open StatMech.Percolation


theorem subcritical_expMomentRadius (b : ℕ) {p : ℝ} (hmean : (b : ℝ) * p < 1) :
    ∃ s, 1 < s ∧ treeGF b p s < s := by
  set g : ℝ → ℝ := fun s => treeGF b p s - s with hg
  have hg1 : g 1 = 0 := by simp [hg]
  have hgder : HasDerivAt g ((b : ℝ) * p - 1) 1 := by
    have := (treeGF_hasDerivAt_one b p).sub (hasDerivAt_id 1)
    simpa [hg] using this
  have hslope : Tendsto (slope g 1) (nhdsWithin 1 {1}ᶜ) (nhds ((b : ℝ) * p - 1)) :=
    hasDerivAt_iff_tendsto_slope.mp hgder
  have hev : ∀ᶠ y in nhdsWithin 1 {1}ᶜ, slope g 1 y < 0 :=
    hslope.eventually_lt_const (by linarith : (b : ℝ) * p - 1 < 0)
  have hsub : nhdsWithin 1 (Ioi (1 : ℝ)) ≤ nhdsWithin 1 {1}ᶜ := by
    refine nhdsWithin_mono _ (fun x hx => ?_)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact ne_of_gt hx
  have hev2 : ∀ᶠ y in nhdsWithin 1 (Ioi (1 : ℝ)), slope g 1 y < 0 := hev.filter_mono hsub
  haveI : (nhdsWithin (1 : ℝ) (Ioi 1)).NeBot := nhdsGT_neBot 1
  obtain ⟨y, hyslope, hymem⟩ := (hev2.and self_mem_nhdsWithin).exists
  have hy1 : (1 : ℝ) < y := hymem
  refine ⟨y, hy1, ?_⟩
  have hslope_eq : slope g 1 y = (g y - g 1) / (y - 1) := slope_def_field g 1 y
  rw [hslope_eq, hg1, sub_zero] at hyslope
  have hypos : (0 : ℝ) < y - 1 := by linarith
  have hgy : g y < 0 := by
    by_contra hcon
    have := div_nonneg (le_of_not_gt hcon) (le_of_lt hypos)
    linarith
  have hgyeq : g y = treeGF b p y - y := rfl
  rw [hgyeq] at hgy; linarith


theorem subcritical_expMomentRadius_of_treeMean (b : ℕ) {p : ℝ}
    (hmean : treeMean b p < 1) : ∃ s, 1 < s ∧ treeGF b p s < s := by
  rw [treeMean] at hmean
  exact subcritical_expMomentRadius b hmean


theorem subcritical_expectedProgeny (b : ℕ) {p : ℝ} (hp0 : 0 ≤ p)
    (hmean : (b : ℝ) * p < 1) :
    ∑' k : ℕ, ((b : ℝ) * p) ^ k = (1 - (b : ℝ) * p)⁻¹ :=
  tsum_geometric_of_lt_one (by positivity) hmean


theorem subcritical_expectedProgeny_pos (b : ℕ) {p : ℝ}
    (hmean : (b : ℝ) * p < 1) : 0 < (1 - (b : ℝ) * p)⁻¹ := by
  have : 0 < 1 - (b : ℝ) * p := by linarith
  positivity


end BeffaraDC
end StatMech

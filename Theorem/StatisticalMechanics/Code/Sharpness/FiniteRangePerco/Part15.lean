/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part15
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem frpSubcriticalSet_nonempty (K : FiniteRangeKernel d) :
    (frpSubcriticalSet K).Nonempty := by
  refine ⟨0, le_rfl, ?_⟩
  intro gamma hgamma0 hgamma
  have hgamma' : gamma = 0 := by linarith
  subst gamma
  refine ⟨{0}, by simp, ?_⟩
  rw [frpPhi_eq_zero_of_nonpos K le_rfl]
  norm_num


theorem exists_frpPhi_witness_of_lt_tildeBetaC (K : FiniteRangeKernel d)
    {beta : ℝ} (hbeta : beta < frpTildeBetaC K) :
    ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ frpPhi K beta S < 1 := by
  by_cases hb0 : beta < 0
  · refine ⟨{0}, by simp, ?_⟩
    rw [frpPhi_eq_zero_of_nonpos K hb0.le]
    norm_num
  · have hb0' : 0 ≤ beta := le_of_not_gt hb0
    unfold frpTildeBetaC at hbeta
    obtain ⟨gamma, hgamma, hbg⟩ :=
      exists_lt_of_lt_csSup (frpSubcriticalSet_nonempty K) hbeta
    exact hgamma.2 beta hb0' hbg.le


theorem frp_subcritical_decay_of_lt_tildeBetaC (K : FiniteRangeKernel d)
    {beta : ℝ} (hbeta : beta < frpTildeBetaC K) :
    ∃ c > 0, ∃ C > 0, ∀ n,
      frpCrossProb K beta n ≤ C * Real.exp (-c * n) := by
  obtain ⟨S, h0S, hphi⟩ := exists_frpPhi_witness_of_lt_tildeBetaC K hbeta
  obtain ⟨N, hSN⟩ := frp_finset_subset_box S
  let L := N + K.range + 1
  have hL : 1 ≤ L := by simp [L]
  have hRL : K.range ≤ L := by
    dsimp [L]
    omega
  have hsub : (S : Set (Site d)) ⊆ box d (L - K.range) := by
    have hcalc : L - K.range = N + 1 := by
      dsimp [L]
      omega
    rw [hcalc]
    exact hSN.trans (box_mono d (Nat.le_succ N))
  exact frp_subcritical_decay K beta S h0S hphi L hL hRL hsub

end Sharpness
end StatMech

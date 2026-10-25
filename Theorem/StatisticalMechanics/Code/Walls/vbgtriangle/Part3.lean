/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/vbgtriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Def.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
open scoped BigOperators
open Finset


namespace StatMech

namespace Walls

namespace VBG

set_option linter.unusedSectionVars false

set_option linter.style.longLine false

set_option maxHeartbeats 800000


variable {Ω : Type*} [Fintype Ω]


section MachineCheck

theorem mc_Y_idem : ∀ ω, mcY ω * mcY ω = mcY ω := by
  intro ω; fin_cases ω <;> simp [mcY]


theorem mc_p_pos : 0 < vbg_exp mcMu mcY := by
  unfold vbg_exp mcMu mcY; simp [Fin.sum_univ_four]; norm_num

theorem mc_p_lt_one : vbg_exp mcMu mcY < 1 := by
  unfold vbg_exp mcMu mcY; simp [Fin.sum_univ_four]; norm_num


theorem mc_prop1 :
    (vbg_var mcMu mcY * vbg_cov mcMu mcX mcZ - vbg_cov mcMu mcX mcY * vbg_cov mcMu mcY mcZ)
        * (vbg_exp mcMu mcY * vbg_varPlus mcMu mcY mcX
            + (1 - vbg_exp mcMu mcY) * vbg_varMinus mcMu mcY mcX)
      = (vbg_exp mcMu mcY * vbg_covPlus mcMu mcY mcX mcZ
            + (1 - vbg_exp mcMu mcY) * vbg_covMinus mcMu mcY mcX mcZ)
        * (vbg_var mcMu mcX * vbg_var mcMu mcY - vbg_cov mcMu mcX mcY ^ 2) :=
  vbg_prop1 mcMu mcX mcY mcZ mc_Y_idem mc_p_pos mc_p_lt_one

end MachineCheck


section GHSRelationship

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem vbg_ghs_distinct (β h : ℝ) (v : V) :
    StatMech.Walls.GhcEqGap.eg_ursell3 G β h v v v
      = 2 * (isingExpectation G β h (fun s => spin s v))^3
        - 2 * isingExpectation G β h (fun s => spin s v) := by
  unfold StatMech.Walls.GhcEqGap.eg_ursell3
  have e_sss : (fun s : ConfigSpace V => spin s v * (spin s v * spin s v))
      = (fun s => spin s v) := by funext s; rw [spin_sq s v, mul_one]
  have e_ss : (fun s : ConfigSpace V => spin s v * spin s v) = (fun _ => (1:ℝ)) := by
    funext s; exact spin_sq s v
  rw [e_sss, e_ss]
  have hone : isingExpectation G β h (fun _ : ConfigSpace V => (1:ℝ)) = 1 := by
    unfold isingExpectation; simp only [mul_one]; exact isingProb_sum_eq_one G β h
  rw [hone]; ring


theorem vbg_cor1_arbitrary_field (β h : ℝ) (hβ : 0 ≤ β) (i j k : V) :
    cov2 G β h i j * cov2 G β h j k
      ≤ vbg_var (isingProb G β h) (fun s => spin s j) * cov2 G β h i k :=
  vbg_cor1 G β h hβ i j k


theorem vbg_ghs_relationship_notes : True := trivial

end GHSRelationship
end VBG
end Walls
end StatMech

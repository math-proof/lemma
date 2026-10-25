/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/Roots.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.SigmaOrder
import Def.v1.Atlas.Buildings.code.CoxeterGroup.Roots
open Finset BigOperators


namespace CoxeterGroup

set_option linter.unusedSectionVars false

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- For distinct simple generators $s \ne t$, the bilinear-form value
$\langle e_s, e_t\rangle = -\cos(\pi/m_{st})$ is nonpositive. -/
theorem formVal_nonpos_of_ne (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) :
    formVal M s t ≤ 0 := by
  unfold formVal
  split
  · linarith
  · rename_i hm0
    have hm1 : M s t ≠ 1 := M.off_diagonal s t hst
    have hm_ge_2 : (2 : ℝ) ≤ (M s t : ℝ) := by
      exact_mod_cast (show M s t ≥ 2 by omega)
    apply neg_nonpos_of_nonneg
    apply Real.cos_nonneg_of_mem_Icc
    have hm_pos : (0 : ℝ) < (M s t : ℝ) := by linarith
    constructor
    · linarith [div_nonneg (le_of_lt Real.pi_pos) (le_of_lt hm_pos), Real.pi_pos]
    · exact div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by positivity) hm_ge_2

/-- For $s \ne t$, $\sigma_s(e_t)$ is a positive root: it stays in the positive cone. -/
theorem sigmaLin_preserves_positive_off_diagonal (M : CoxeterMatrix B) (s t : B) (hst : s ≠ t) :
    IsPositive (sigmaLin M s (e t)) := by
  rw [sigmaLin_e M s t hst]
  intro u
  simp only [e, Pi.single_apply]
  have hfv : formVal M s t ≤ 0 := formVal_nonpos_of_ne M s t hst
  split_ifs <;> nlinarith

/-- For $t \ne s$, the $t$-coordinate of $\sigma_s(v)$ equals $v(t)$ (reflection fixes other coords). -/
theorem sigma_coord_ne (M : CoxeterMatrix B) (s : B) (v : B → ℝ) (t : B) (hts : t ≠ s) :
    sigma M s v t = v t := by
  simp only [sigma, e, Pi.single_apply, if_neg hts, mul_zero, sub_zero]

/-- The $s$-coordinate of $\sigma_s(v)$ is $v(s) - 2\langle v, e_s\rangle$. -/
theorem sigma_coord_self (M : CoxeterMatrix B) (s : B) (v : B → ℝ) :
    sigma M s v s = v s - 2 * bilinForm M v (e s) := by
  simp only [sigma, e, Pi.single_apply, if_true, mul_one]

end CoxeterGroup

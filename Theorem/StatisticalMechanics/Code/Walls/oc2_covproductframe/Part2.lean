/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covproductframe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Def.StatisticalMechanics.Code.Walls.oc2_covproductframe
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.CovLowerBound

variable {E : Type*} [Fintype E] [DecidableEq E]

variable {ν : E → Bool → ℝ}


theorem oc2_corOSSS_RHS_frame (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ) :
    oc2_CovProductFrame ν f (expect ν f) (∑ e, cov ν (coordI e) f) :=
  ⟨rfl, rfl⟩


theorem oc2_covProductFrame_sum_frame (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ) :
    (∑ e, cov ν (coordI e) f)
      = ∑ e, (expect ν (fun ω => coordI e ω * f ω) - expect ν (coordI e) * expect ν f) :=
  Finset.sum_congr rfl (fun e _ => oc2_cov_coordI_frame ν e f)


theorem oc2_covProductFrame_sum_bernoulli (hν : IsProbWeight ν) (f : ConfigSpace E → ℝ) :
    (∑ e, cov ν (coordI e) f)
      = ∑ e, (expect ν (fun ω => coordI e ω * f ω) - ν e true * expect ν f) :=
  Finset.sum_congr rfl (fun e _ => oc2_cov_coordI_bernoulli hν e f)

end Walls
end StatMech

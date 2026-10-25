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
import Theorem.StatisticalMechanics.Code.Walls.oc2_covproductframe
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


def oc2_CovProductFrame (ν : E → Bool → ℝ) (f : ConfigSpace E → ℝ) (θ covCorr : ℝ) : Prop :=
  covCorr = ∑ e, cov ν (coordI e) f ∧ θ = expect ν f


end Walls
end StatMech

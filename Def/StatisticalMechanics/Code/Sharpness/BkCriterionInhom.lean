/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInhom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerEndpointProve.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInhom
open scoped BigOperators
open Finset


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

variable {E V : Type*}


noncomputable def shk_edgeLaw (beta : ℝ) (J : E → ℝ) (e : E) (b : Bool) : ℝ :=
  if b then 1 - Real.exp (-beta * J e) else Real.exp (-beta * J e)

end Sharpness
end StatMech

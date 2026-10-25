/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
open Filter Finset Set Topology


namespace StatMech.FrontierA

noncomputable section

theorem exists_le_two_pow (x : Real) :
    ∃ n : Nat, x ≤ (2 : Real) ^ n := by
  have h := (tendsto_pow_atTop_atTop_of_one_lt
    (r := (2 : Real)) (by norm_num)).eventually (eventually_ge_atTop x)
  exact h.exists


end
end StatMech.FrontierA

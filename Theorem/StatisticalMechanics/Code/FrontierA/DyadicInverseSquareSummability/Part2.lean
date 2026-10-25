/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/DyadicInverseSquareSummability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Def.StatisticalMechanics.Code.FrontierA.DyadicInverseSquareSummability
open Filter Finset Set Topology


namespace StatMech.FrontierA

noncomputable section

theorem size_le_two_pow_dyadicUpperLevel
    {Q : Type*} (size : Q → Real) (q : Q) :
    size q ≤ (2 : Real) ^ dyadicUpperLevel size q :=
  Nat.find_spec (exists_le_two_pow (size q))

theorem two_pow_lt_size_of_lt_dyadicUpperLevel
    {Q : Type*} (size : Q → Real) (q : Q) {n : Nat}
    (hn : n < dyadicUpperLevel size q) :
    (2 : Real) ^ n < size q := by
  by_contra h
  have hle : size q ≤ (2 : Real) ^ n := le_of_not_gt h
  have := Nat.find_min' (exists_le_two_pow (size q)) hle
  exact (Nat.not_le_of_lt hn) this


end
end StatMech.FrontierA

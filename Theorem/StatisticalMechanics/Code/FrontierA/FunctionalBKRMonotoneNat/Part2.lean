/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRMonotoneNat.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFinite.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRMonotoneNat.Part2
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


theorem lt_natFunctionBound (F : ConfigSpace E -> ℕ) (omega : ConfigSpace E) :
    F omega < natFunctionBound F := by
  unfold natFunctionBound
  exact Nat.lt_succ_of_le (Finset.le_sup' F (Finset.mem_univ omega))


end StatMech.FrontierA

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStaircaseAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIncidentStairPatch.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardStaircaseAssembly.Part3


namespace StatMech.FrontierA

open scoped NNReal

open Set


theorem kwStairSliceIndex_even {S : ℕ} [NeZero S] (k : Fin S) :
    kwStairSliceIndex (kwStairEvenLocal k) = k := by
  apply Fin.ext
  simp [kwStairSliceIndex, kwStairEvenLocal]

theorem kwStairSliceIndex_odd {S : ℕ} [NeZero S] (k : Fin S) :
    kwStairSliceIndex (kwStairOddLocal k) = k := by
  apply Fin.ext
  simp only [kwStairSliceIndex, kwStairOddLocal]
  omega

@[simp] theorem kwStairEvenLocal_mod_two
    {S : ℕ} [NeZero S] (k : Fin S) :
    (kwStairEvenLocal k).val % 2 = 0 := by
  simp [kwStairEvenLocal]

@[simp] theorem kwStairOddLocal_mod_two
    {S : ℕ} [NeZero S] (k : Fin S) :
    (kwStairOddLocal k).val % 2 = 1 := by
  simp [kwStairOddLocal]

end StatMech.FrontierA

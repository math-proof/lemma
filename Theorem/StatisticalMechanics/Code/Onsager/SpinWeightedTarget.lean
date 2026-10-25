/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedBounds
import Theorem.StatisticalMechanics.Code.Onsager.KWMultiaffineBounded
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientTarget.Part2
import Def.StatisticalMechanics.Code.Onsager.SpinWeightedTarget


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

theorem ons_weightedSpinCharacterSum_const
    (L : ℕ) [Fact (2 < L)] (x : ℝ) (a b : Fin 2) :
    ons_weightedSpinCharacterSum L (fun _ => (x : ℂ)) a b =
      (ons_spinCharacterSum L x a b : ℂ) := by
  unfold ons_weightedSpinCharacterSum ons_spinCharacterSum
  push_cast
  apply Finset.sum_congr rfl
  intro F hF
  simp


end StatMech.Onsager

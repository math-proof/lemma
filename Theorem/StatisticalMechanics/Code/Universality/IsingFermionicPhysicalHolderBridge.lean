/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalHolderBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy.Part4
import Def.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalHolderBridge


namespace StatMech.Universality

open Finset

noncomputable section

theorem fkIsingSquareRadialPatchDeepVariation_nonneg
    (n m : Nat) (hn : 0 < n) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (r : Nat) (base : Real) :
    0 ≤ fkIsingSquareRadialPatchDeepVariation n m hn hm hm2 r base := by
  unfold fkIsingSquareRadialPatchDeepVariation
  positivity


end
end StatMech.Universality

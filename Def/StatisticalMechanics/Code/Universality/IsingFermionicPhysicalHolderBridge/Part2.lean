/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalHolderBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDeepEnergy.Part4
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalHolderBridge


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def fkIsingSquareRadialPatchPhysicalNormalizedWindow
    (n m baseI baseJ R : Nat) (mesh : Real)
    (hn : 0 < n) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogBox R → Complex :=
  fun p ↦ fkIsingSquareRadialPatchFullObservableWindow
      n m baseI baseJ R hn hm hfitI hfitJ p /
    (Real.sqrt (2 * mesh) : Complex)


end
end StatMech.Universality

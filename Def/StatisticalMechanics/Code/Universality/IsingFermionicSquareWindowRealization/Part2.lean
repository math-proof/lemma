/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWindowRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalAverageAnchor
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization.Part2


namespace StatMech.Universality

open Finset

noncomputable section

def fkIsingSquareRadialPatchWindowCarrierEmbedding
    (n m baseI baseJ R : Nat) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    IsingLeapfrogBox R ↪ FKIsingSquareWiredCarrier n where
  toFun := fkIsingSquareRadialPatchWindowCarrier
    n m baseI baseJ R hm hfitI hfitJ
  inj' := fkIsingSquareRadialPatchWindowCarrier_injective
    n m baseI baseJ R hm hfitI hfitJ


end
end StatMech.Universality

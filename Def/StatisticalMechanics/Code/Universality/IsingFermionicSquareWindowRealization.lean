/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWindowRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalAverageAnchor
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization


namespace StatMech.Universality

open Finset

noncomputable section

def fkIsingSquareRadialPatchWindowCarrier
    (n m baseI baseJ R : Nat) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m)
    (p : IsingLeapfrogBox R) : FKIsingSquareWiredCarrier n :=
  .dart
    (fkIsingSquareRadialPatchEdge n m hm
      ⟨baseI + p.1.1, by have := p.1.2; omega⟩
      ⟨baseJ + p.2.1, by have := p.2.2; omega⟩, .west)

end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part4


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareWiredBoundaryEmbedding (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredBoundaryDartIndex n ↪
      FKIsingMedialDart (fkSquareBoxPlanar n) :=
  ⟨fkIsingSquareWiredBoundaryDart n hn,
    fkIsingSquareWiredBoundaryDart_injective n hn⟩

def fkIsingSquareWiredShift (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredBoundaryDartIndex n →
      FKIsingSquareWiredBoundaryDartIndex n
  | .bottom => .bottom
  | .west k => if hk : k.val = 0 then .top
      else .north ⟨k.val - 1, by omega⟩
  | .north k => .west k
  | .top => .north ⟨2 * n - 1, by omega⟩

def fkIsingSquareWiredShiftInv (n : Nat) (hn : 0 < n) :
    FKIsingSquareWiredBoundaryDartIndex n →
      FKIsingSquareWiredBoundaryDartIndex n
  | .bottom => .bottom
  | .west k => .north k
  | .north k => if hk : k.val + 1 < 2 * n then
      .west ⟨k.val + 1, hk⟩ else .top
  | .top => .west ⟨0, by omega⟩

end
end StatMech.Universality

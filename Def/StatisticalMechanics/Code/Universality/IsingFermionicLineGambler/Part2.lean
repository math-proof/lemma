/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler


namespace StatMech.Universality

open Finset

noncomputable section

def isingLineWest (n : Nat) (p : IsingLineBox n) : IsingLineBox n :=
  ⟨p.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) p.2⟩

def isingLineEast (n : Nat) (p : IsingLineBox n)
    (hp : ¬ isingLineBoxBoundary n p) : IsingLineBox n :=
  ⟨p.1 + 1, by
    have hle := p.2
    unfold isingLineBoxBoundary at hp
    omega⟩


noncomputable def isingLineStoppedKernel (n : Nat) :
    Nat → IsingLineBox n → IsingLineBox n → Real
  | 0, p, q => if p = q then 1 else 0
  | t + 1, p, q =>
      if hp : isingLineBoxBoundary n p then
        isingLineStoppedKernel n t p q
      else
        (isingLineStoppedKernel n t (isingLineWest n p) q +
          isingLineStoppedKernel n t (isingLineEast n p hp) q) / 2

end
end StatMech.Universality

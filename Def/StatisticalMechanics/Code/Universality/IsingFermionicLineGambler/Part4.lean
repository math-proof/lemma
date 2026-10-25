/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part2


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def isingLineChoiceNext (n : Nat) (p : IsingLineBox n)
    (b : Bool) : IsingLineBox n :=
  if hp : isingLineBoxBoundary n p then p
  else if b then isingLineEast n p hp else isingLineWest n p

noncomputable def isingLineChoiceRun (n : Nat) :
    IsingLineBox n → List Bool → IsingLineBox n
  | p, [] => p
  | p, b :: bs => isingLineChoiceRun n (isingLineChoiceNext n p b) bs

def IsingLineChoicePathFamily (n t : Nat)
    (p q : IsingLineBox n) :=
  {bs : List Bool // bs.length = t ∧ isingLineChoiceRun n p bs = q}

end
end StatMech.Universality

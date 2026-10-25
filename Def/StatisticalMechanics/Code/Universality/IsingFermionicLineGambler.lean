/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Abbrev.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler


namespace StatMech.Universality

open Finset

noncomputable section

def isingLineBoxBoundary (n : Nat) (p : IsingLineBox n) : Prop :=
  p.1 = 0 ∨ p.1 = n

end
end StatMech.Universality

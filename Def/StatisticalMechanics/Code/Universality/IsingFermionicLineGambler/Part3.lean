/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part17
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler


namespace StatMech.Universality

open Finset

noncomputable section

noncomputable def isingLineStoppedMean (n t : Nat)
    (f : IsingLineBox n → Real) (p : IsingLineBox n) : Real :=
  ∑ q, isingLineStoppedKernel n t p q * f q

def IsingLineHarmonic (n : Nat) (f : IsingLineBox n → Real) : Prop :=
  ∀ p (hp : ¬ isingLineBoxBoundary n p),
    f (isingLineWest n p) + f (isingLineEast n p hp) = 2 * f p

end
end StatMech.Universality

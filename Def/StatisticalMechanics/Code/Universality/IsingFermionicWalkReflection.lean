/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9


namespace StatMech.Universality

def isingDiagonalWalkDisplacement (steps : List (Int × Int)) : Int × Int :=
  ((steps.map Prod.fst).sum, (steps.map Prod.snd).sum)


def isingDiagonalWalkEndpoint (start : Int × Int)
    (steps : List (Int × Int)) : Int × Int :=
  (start.1 + (isingDiagonalWalkDisplacement steps).1,
    start.2 + (isingDiagonalWalkDisplacement steps).2)


def IsingDiagonalWalkStepsValid (steps : List (Int × Int)) : Prop :=
  ∀ d ∈ steps, (d.1 = 1 ∨ d.1 = -1) ∧ (d.2 = 1 ∨ d.2 = -1)


end StatMech.Universality

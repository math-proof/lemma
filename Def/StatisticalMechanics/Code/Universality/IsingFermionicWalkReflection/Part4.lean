/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part2


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}

def endpoint (w : IsingDiagonalWalkHitSplit start level) : Int × Int :=
  isingDiagonalWalkEndpoint start w.steps

def Valid (w : IsingDiagonalWalkHitSplit start level) : Prop :=
  IsingDiagonalWalkStepsValid w.steps

def reflectIncrement (d : Int × Int) : Int × Int :=
  (-d.1, d.2)


def reflect (w : IsingDiagonalWalkHitSplit start level) :
    IsingDiagonalWalkHitSplit start level where
  before := w.before
  after := w.after.map reflectIncrement
  hit := w.hit

end IsingDiagonalWalkHitSplit
end StatMech.Universality

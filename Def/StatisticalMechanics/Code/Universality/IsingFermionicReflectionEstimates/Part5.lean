/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflectionEstimates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part4


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

def rightGapNeighbor (R level : Nat)
    (hgap : level + 1 < R) : IsingLineBox (R - level) :=
  ⟨R - level - 1, by omega⟩

def rightGapLeft (R level : Nat) : IsingLineBox (R - level) :=
  ⟨0, by omega⟩

end IsingDiagonalWalkHitSplit
end StatMech.Universality

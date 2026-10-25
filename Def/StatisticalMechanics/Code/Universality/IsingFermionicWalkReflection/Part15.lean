/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicWalkReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKilledKernel.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWalkReflection.Part13


namespace StatMech.Universality

namespace IsingDiagonalWalkHitSplit

variable {start : Int × Int} {level : Int}


def InOpenBox (R : Nat) (z : Int × Int) : Prop :=
  0 < z.1 ∧ z.1 < R ∧ 0 < z.2 ∧ z.2 < R


def StaysInOpenBox (R : Nat) (start : Int × Int)
    (path : List (Int × Int)) : Prop :=
  ∀ k, k ≤ path.length →
    InOpenBox R (isingDiagonalWalkEndpoint start (path.take k))

end IsingDiagonalWalkHitSplit
end StatMech.Universality

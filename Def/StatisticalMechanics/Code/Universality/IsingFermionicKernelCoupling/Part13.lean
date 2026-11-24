module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def IsingHorizontalNoHitFamily (t : Nat) (start level : Int) :=
  {bs : List Bool // bs.length = t ∧
    ∀ k, k ≤ t →
      lineFreeEndpoint start (bs.take k) ≠ level}

end
end StatMech.Universality

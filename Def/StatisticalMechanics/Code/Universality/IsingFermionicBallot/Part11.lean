module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/
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

def HorizontalCentralBand (t : Nat) (level : Int) :=
  {w : HorizontalFreeBelow t (level - 1) level //
    ¬ lineFreeEndpoint (level - 1) w.1 < level - 2}

end
end StatMech.Universality

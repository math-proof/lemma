module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part17


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/
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

def isingLeapfrogFlipXChoices (bs : List (Bool × Bool)) : List (Bool × Bool) :=
  bs.map (fun b => (!b.1, b.2))

end
end StatMech.Universality

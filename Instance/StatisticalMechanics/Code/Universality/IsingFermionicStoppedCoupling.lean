module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part2


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

noncomputable instance isingLeapfrogChoiceStringFamily_finite (t : Nat) :
    Finite (IsingLeapfrogChoiceStringFamily t) :=
  List.finite_length_eq (Bool × Bool) t

end
end StatMech.Universality

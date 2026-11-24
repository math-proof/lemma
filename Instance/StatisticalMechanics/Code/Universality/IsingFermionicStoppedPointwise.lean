module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open IsingDiagonalWalkHitSplit

noncomputable instance isingLeapfrogStoppedCouplingBadAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level) := by
  exact Finite.of_injective
    (fun w : IsingLeapfrogStoppedCouplingBadAtFamily R t p p' q level => w.1)
    Subtype.val_injective


end StatMech.Universality

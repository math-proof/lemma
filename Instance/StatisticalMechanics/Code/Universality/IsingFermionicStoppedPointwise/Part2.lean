/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part22
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedPointwise.Part2


namespace StatMech.Universality

open IsingDiagonalWalkHitSplit

noncomputable instance isingLeapfrogChoiceNoHitAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingLeapfrogChoiceNoHitAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance isingStoppedCouplingSourceFailureAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite
      (IsingStoppedCouplingSourceFailureAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance isingStoppedCouplingMirrorFailureAtFamily_finite
    (R t : Nat) (p p' q : IsingLeapfrogBox R) (level : Int) :
    Finite
      (IsingStoppedCouplingMirrorFailureAtFamily R t p p' q level) := by
  exact Finite.of_injective Subtype.val Subtype.val_injective

end StatMech.Universality

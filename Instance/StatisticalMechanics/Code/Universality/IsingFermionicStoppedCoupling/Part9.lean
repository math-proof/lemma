/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part14
import Def.StatisticalMechanics.Code.Universality.IsingFermionicStoppedCoupling.Part18


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

noncomputable instance sourceFailureFamily_finite
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingStoppedCouplingSourceFailureFamily R t p level) := by
  exact Finite.of_injective
    (fun w : IsingStoppedCouplingSourceFailureFamily R t p level => w.1)
    Subtype.val_injective

noncomputable instance mirrorFailureFamily_finite
    (R t : Nat) (p p' : IsingLeapfrogBox R) (level : Int) :
    Finite (IsingStoppedCouplingMirrorFailureFamily R t p p' level) := by
  exact Finite.of_injective
    (fun w : IsingStoppedCouplingMirrorFailureFamily R t p p' level => w.1)
    Subtype.val_injective

end
end StatMech.Universality

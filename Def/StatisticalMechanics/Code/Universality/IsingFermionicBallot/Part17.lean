module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part13


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

def survivalExceptionalMirrorBoxSigmaToAll
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    SurvivalExceptionalMirrorBoxSigma R t p level →
      SurvivalExceptionalMirrorFamilyAll R (isingLeapfrogBoxInt p) level t :=
  fun w => ⟨isingLeapfrogBoxInt w.1, w.2⟩

end
end StatMech.Universality

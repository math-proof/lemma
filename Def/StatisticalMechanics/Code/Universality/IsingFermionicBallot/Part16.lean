/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part12


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def SurvivalExceptionalFirstHitBoxSigma
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :=
  Σ q : IsingLeapfrogBox R,
    SurvivalExceptionalFirstHitFamily R (isingLeapfrogBoxInt p) level t
      (isingLeapfrogBoxInt q)

def SurvivalExceptionalMirrorBoxSigma
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :=
  Σ q : IsingLeapfrogBox R,
    SurvivalExceptionalMirrorFamily R (isingLeapfrogBoxInt p) level t
      (isingLeapfrogBoxInt q)

def survivalExceptionalFirstHitBoxSigmaToAll
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    SurvivalExceptionalFirstHitBoxSigma R t p level →
      SurvivalExceptionalFirstHitFamilyAll R (isingLeapfrogBoxInt p) level t :=
  fun w => ⟨isingLeapfrogBoxInt w.1, w.2⟩

end
end StatMech.Universality

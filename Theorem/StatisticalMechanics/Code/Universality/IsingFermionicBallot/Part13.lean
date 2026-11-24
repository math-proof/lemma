module
public import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
public import Def.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part16


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

theorem survivalExceptionalFirstHitBoxSigmaToAll_injective
    (R t : Nat) (p : IsingLeapfrogBox R) (level : Int) :
    Function.Injective
      (survivalExceptionalFirstHitBoxSigmaToAll R t p level) := by
  intro a b h
  rcases Sigma.ext_iff.mp h with ⟨htarget, hw⟩
  exact Sigma.ext (isingLeapfrogBoxInt_injective htarget) hw

end
end StatMech.Universality

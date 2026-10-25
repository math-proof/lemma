/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBallot.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part10
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicBallot.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def horizontalFreeBelowHitNoHitEquiv
    (t : Nat) (start level : Int) :
    HorizontalFreeBelow t start level ≃
      HorizontalHitBelow t start level ⊕
        HorizontalNoHitBelow t start level :=
  (Equiv.sumCompl (fun w : HorizontalFreeBelow t start level =>
    isingDiagonalWalkFirstHitSplit? (start, 0) level
      (horizontalChoiceSteps w.1) ≠ none)).symm


def HorizontalFirstHitBelow (t : Nat) (start level : Int) :=
  {w : IsingDiagonalWalkHitSplit (start, 0) level //
    w.FirstHit ∧ w.Valid ∧ w.steps.length = t ∧
      w.endpoint.1 < level ∧ ∀ d ∈ w.steps, d.2 = 1}

noncomputable def horizontalHitBelowSplit
    {t : Nat} {start level : Int}
    (z : HorizontalHitBelow t start level) :
    IsingDiagonalWalkHitSplit (start, 0) level :=
  (isingDiagonalWalkFirstHitSplit? (start, 0) level
    (horizontalChoiceSteps z.1.1)).get
      (Option.ne_none_iff_isSome.mp z.2)

end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk.Part4


namespace StatMech.Universality

open Finset

noncomputable section

def IsingLeapfrogInteriorMargin (R ρ : Nat) (p : IsingLeapfrogBox R) : Prop :=
  ρ ≤ p.1.1 ∧ p.1.1 + ρ ≤ R ∧
    ρ ≤ p.2.1 ∧ p.2.1 + ρ ≤ R


def IsingLeapfrogDiagonalAdjacent {R : Nat}
    (p p' : IsingLeapfrogBox R) : Prop :=
  Nat.dist p.1.1 p'.1.1 = 1 ∧ Nat.dist p.2.1 p'.2.1 = 1


def IsingLeapfrogDiffusiveGradientBound (C : Real) : Prop :=
  0 ≤ C ∧
    ∀ (R ρ : Nat) (p p' : IsingLeapfrogBox R),
      0 < ρ →
      IsingLeapfrogInteriorMargin R ρ p →
      IsingLeapfrogInteriorMargin R ρ p' →
      IsingLeapfrogDiagonalAdjacent p p' →
      isingLeapfrogStoppedKernelTimeGradientSq R
          (ρ * ρ) (ρ * ρ + 1) p p' ≤
        C / (ρ : Real) ^ 3


def IsingLeapfrogDiffusiveKernelInputs (A B : Real) : Prop :=
  0 ≤ A ∧ 0 ≤ B ∧
    ∀ (R ρ : Nat) (p p' : IsingLeapfrogBox R),
      0 < ρ →
      IsingLeapfrogInteriorMargin R ρ p →
      IsingLeapfrogInteriorMargin R ρ p' →
      IsingLeapfrogDiagonalAdjacent p p' →
      (∀ q, |isingLeapfrogStoppedKernel R (ρ * ρ) p q -
          isingLeapfrogStoppedKernel R (ρ * ρ + 1) p' q| ≤
        A / (ρ : Real) ^ 2) ∧
      (∑ q, |isingLeapfrogStoppedKernel R (ρ * ρ) p q -
          isingLeapfrogStoppedKernel R (ρ * ρ + 1) p' q|) ≤
        B / (ρ : Real)

end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicStoppedWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity.Part3
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicStoppedWalk


namespace StatMech.Universality

open Finset

noncomputable section

def isingLeapfrogWest (R : Nat) (p : IsingLeapfrogBox R) : Fin (R + 1) :=
  ⟨p.1.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) p.1.2⟩

def isingLeapfrogSouth (R : Nat) (p : IsingLeapfrogBox R) : Fin (R + 1) :=
  ⟨p.2.1 - 1, lt_of_le_of_lt (Nat.sub_le _ _) p.2.2⟩

def isingLeapfrogEast (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : Fin (R + 1) :=
  ⟨p.1.1 + 1, by
    have hle := p.1.2
    unfold isingLeapfrogBoxBoundary at hp
    omega⟩

def isingLeapfrogNorth (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : Fin (R + 1) :=
  ⟨p.2.1 + 1, by
    have hle := p.2.2
    unfold isingLeapfrogBoxBoundary at hp
    omega⟩

def isingLeapfrogSW (R : Nat) (p : IsingLeapfrogBox R) :
    IsingLeapfrogBox R :=
  (isingLeapfrogWest R p, isingLeapfrogSouth R p)

def isingLeapfrogSE (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : IsingLeapfrogBox R :=
  (isingLeapfrogEast R p hp, isingLeapfrogSouth R p)

def isingLeapfrogNW (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : IsingLeapfrogBox R :=
  (isingLeapfrogWest R p, isingLeapfrogNorth R p hp)

def isingLeapfrogNE (R : Nat) (p : IsingLeapfrogBox R)
    (hp : ¬ isingLeapfrogBoxBoundary R p) : IsingLeapfrogBox R :=
  (isingLeapfrogEast R p hp, isingLeapfrogNorth R p hp)


def IsingLeapfrogHarmonicOnBox (R : Nat)
    (f : IsingLeapfrogBox R → Complex) : Prop :=
  ∀ p (hp : ¬ isingLeapfrogBoxBoundary R p),
    f (isingLeapfrogSW R p) + f (isingLeapfrogNW R p hp) +
        f (isingLeapfrogSE R p hp) + f (isingLeapfrogNE R p hp) =
      4 * f p


noncomputable def isingLeapfrogStoppedKernel (R : Nat) :
    Nat → IsingLeapfrogBox R → IsingLeapfrogBox R → Real
  | 0, p, q => if p = q then 1 else 0
  | t + 1, p, q =>
      if hp : isingLeapfrogBoxBoundary R p then
        isingLeapfrogStoppedKernel R t p q
      else
        (isingLeapfrogStoppedKernel R t (isingLeapfrogSW R p) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogSE R p hp) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogNW R p hp) q +
          isingLeapfrogStoppedKernel R t (isingLeapfrogNE R p hp) q) / 4

end
end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
open Filter Topology Set
open scoped BigOperators Topology


namespace StatMech.FrontierA

noncomputable section

def rectangularSurfaceDensity (F : Nat → Nat → Real) (m n : Nat) : Real :=
  F m n / ((m : Real) * (n : Real))


def positiveRectangularSurfaceDensities
    (F : Nat → Nat → Real) : Set Real :=
  {x | ∃ m n : Nat, 0 < m ∧ 0 < n ∧ rectangularSurfaceDensity F m n = x}


def rectangularSurfaceRate (F : Nat → Nat → Real) : Real :=
  sInf (positiveRectangularSurfaceDensities F)


def HasRectangularBlockGluing (F : Nat → Nat → Real) : Prop :=
  ∀ m k : Nat, 0 < m → 0 < k →
    ∃ C : Real, 0 ≤ C ∧ ∀ n : Nat, 0 < n →
      rectangularSurfaceDensity F n n ≤
        rectangularSurfaceDensity F m k + C / n


def HorizontallySubadditive (F : Nat → Nat → Real) : Prop :=
  ∀ k : Nat, Subadditive (fun m => F m k)


def VerticallySubadditive (F : Nat → Nat → Real) : Prop :=
  ∀ m : Nat, Subadditive (F m)


end
end StatMech.FrontierA

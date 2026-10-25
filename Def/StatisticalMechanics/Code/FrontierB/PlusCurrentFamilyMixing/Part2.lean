/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusCurrentFamilyMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentSingletonMixing
import Theorem.StatisticalMechanics.Code.FrontierB.PlusCurrentFamilyMixing.Part2
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierB

open Sharpness Ising Lattice

open StatMech.ConfigSpace StatMech.FK


def liftCurrentPatternSet {E : Type*} {S U : Finset E} (hSU : S ⊆ U)
    (A : Set (↑S -> Nat)) : Set (↑U -> Nat) :=
  {a | Finset.restrict₂ (π := fun _ : E => Nat) hSU a ∈ A}

end StatMech.FrontierB

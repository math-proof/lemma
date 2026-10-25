/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentPairCylinders.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.JointCurrentSubsequence
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentPairCylinders
open Filter MeasureTheory Topology


namespace StatMech.FrontierB

variable {E : Type*} [Countable E]

def currentPairCylinder (S : Finset E) (A : Set ((↑S → ℕ) × (↑S → ℕ))) :
    Set (InfiniteCurrentConfig E × InfiniteCurrentConfig E) :=
  restrictCurrentPair S ⁻¹' A

end StatMech.FrontierB

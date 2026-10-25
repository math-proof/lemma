/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteLocalSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentPairCylinders.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
import Theorem.StatisticalMechanics.Code.FrontierB.FiniteLocalSwitching
open scoped symmDiff


namespace StatMech.FrontierB

open Sharpness

open Finset MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {E : Type*} [Countable E]

def currentSuperpositionCylinder (S : Finset E) (A : Set (↑S → ℕ)) :
    Set (InfiniteCurrentConfig E × InfiniteCurrentConfig E) :=
  currentPairCylinder S
    {p | (fun e => p.1 e + p.2 e) ∈ A}

end StatMech.FrontierB

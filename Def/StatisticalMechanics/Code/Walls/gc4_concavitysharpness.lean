/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_concavitysharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.ghc_twicediff
import Theorem.StatisticalMechanics.Code.Walls.gc_core.Part2
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def gc4_D1cov2 (β h : ℝ) (o x : V) : ℝ :=
    (β * (isingExpectation G β h (fun s => (spin s o * spin s x) * totalSpin s)
        - isingExpectation G β h (fun s => spin s o * spin s x) * isingExpectation G β h totalSpin))
    - ((β * (isingExpectation G β h (fun s => spin s o * totalSpin s)
            - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpin))
          * isingExpectation G β h (fun s => spin s x)
        + isingExpectation G β h (fun s => spin s o)
          * (β * (isingExpectation G β h (fun s => spin s x * totalSpin s)
              - isingExpectation G β h (fun s => spin s x) * isingExpectation G β h totalSpin)))


end StatMech.Walls

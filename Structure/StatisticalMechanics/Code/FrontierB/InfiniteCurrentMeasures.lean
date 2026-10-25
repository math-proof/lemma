/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentMeasures.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentPairCylinders.Part2
open Filter MeasureTheory


namespace StatMech.FrontierB

open Lattice

structure FreePlusCurrentLimitData (d : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) where
  freeLimit : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))
  plusLimit : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))
  subsequence : ℕ → ℕ
  strictMono_subsequence : StrictMono subsequence
  free_tendsto : WeakCurrentConverges
    ((fun n => freeBoxCurrentMeasure d n beta hbeta) ∘ subsequence) freeLimit
  plus_tendsto : WeakCurrentConverges
    ((fun n => plusBoxCurrentMeasure d n beta hbeta) ∘ subsequence) plusLimit

end StatMech.FrontierB

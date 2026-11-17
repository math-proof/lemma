/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part5
public section

open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


structure GeneralInteractionCurrentLimitData {d : Nat}
    (I : SummableFerromagneticInteraction d)
    (beta : Real) (hbeta : 0 <= beta) where
  freeLimit : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))
  plusLimit : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d)))
  subsequence : Nat -> Nat
  strictMono_subsequence : StrictMono subsequence
  free_tendsto : WeakCurrentConverges
    ((fun n => generalFreeBoxCurrentMeasure
      I.coupling I.nonneg n beta hbeta) ∘ subsequence) freeLimit
  plus_tendsto : WeakCurrentConverges
    ((fun n => generalPlusBoxCurrentMeasure
      I.coupling I.nonneg n beta hbeta) ∘ subsequence) plusLimit


end StatMech.FrontierB

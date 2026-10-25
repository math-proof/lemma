/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part10
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure PairedAlignedMixedLevelStep
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Nat -> Finset V) (Sdual : Nat -> Finset W)
    (p pDual : Nat -> Real)
    (family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (familyDual : forall m,
      Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m))
    (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
    (previousScale previousConnector : Nat)
    (scoreEpsilon mergeEpsilon : Real) where
  scale : Nat
  scale_ge : previousScale <= scale
  primal_threshold_gt : 1 - scoreEpsilon < p scale
  dual_threshold_gt : 1 - scoreEpsilon < pDual scale
  schedule : PairedAlignedMarginSchedule E Edual
    (family scale) (familyDual scale)
    (verticalRequirement scale) (horizontalRequirement scale)
  mixed : PairedMixedBoundaryScores E Edual mu muDual
    (S scale) (Sdual scale) (p scale) (pDual scale)
  rotated : PairedMixedBoundaryScores E.axisSwap Edual.axisSwap mu muDual
    (S scale) (Sdual scale) (p scale) (pDual scale)
  nextConnector : Nat
  connector_mono : previousConnector <= nextConnector
  primalVerticalMerge : mu.real (P.pairMergeErrorUnion
    mixed.primalBottomSource mixed.primalTopSource nextConnector) <
      mergeEpsilon
  primalHorizontalMerge : mu.real (P.pairMergeErrorUnion
    mixed.primalLeftSource mixed.primalRightSource nextConnector) <
      mergeEpsilon
  dualVerticalMerge : muDual.real (Pdual.pairMergeErrorUnion
    mixed.dualBottomSource mixed.dualTopSource nextConnector) < mergeEpsilon
  dualHorizontalMerge : muDual.real (Pdual.pairMergeErrorUnion
    mixed.dualLeftSource mixed.dualRightSource nextConnector) < mergeEpsilon


end StatMech.FK.PeriodicPlanar

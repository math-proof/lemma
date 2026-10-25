/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part6
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure AlignedCrossNestedThreePairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k padding : Nat) where
  previousX : Nat
  previousY : Nat
  currentX : Nat
  currentY : Nat
  nextX : Nat
  nextY : Nat
  previous : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual family familyDual schedule k previousX previousY
  current : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual family familyDual schedule k currentX currentY
  next : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual family familyDual schedule k nextX nextY
  currentX_eq : (currentX : Int) = previous.raw.wideRightInt -
    previous.raw.wideLeftInt + 2 * padding
  nextX_eq : (nextX : Int) = current.raw.wideRightInt -
    current.raw.wideLeftInt + 2 * padding
  previousY_eq : previousY = currentY + 2 * padding
  currentY_eq : currentY = nextY + 2 * padding


end StatMech.FK.PeriodicPlanar

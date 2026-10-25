/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure AlignedNormalTwoRotatedEndpointPairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat -> Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) where
  normalX : Nat
  normalY : Nat
  rotatedHorizontalX : Nat
  rotatedHorizontalY : Nat
  normal : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual family familyDual schedule k normalX normalY
  rotatedVertical : AlignedExactExtentPairedMixedBoundaryScores
    E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
    family.axisSwap familyDual.axisSwap schedule.axisSwap k normalY normalX
  rotatedHorizontal : AlignedExactExtentPairedMixedBoundaryScores
    E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual
    family.axisSwap familyDual.axisSwap schedule.axisSwap k
    rotatedHorizontalX rotatedHorizontalY
  normalSpan_eq : normal.raw.wideRightInt - normal.raw.wideLeftInt =
    rotatedHorizontalY
  rotatedHorizontalSpan_eq :
    rotatedHorizontal.raw.wideRightInt -
      rotatedHorizontal.raw.wideLeftInt = normalY


end StatMech.FK.PeriodicPlanar

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part9
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure CrossNestedThreePairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real)
    (padding : Nat) where
  previousX : Nat
  previousY : Nat
  currentX : Nat
  currentY : Nat
  nextX : Nat
  nextY : Nat
  previous : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual previousX previousY
  current : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual currentX currentY
  next : ExactExtentPairedMixedBoundaryScores E Edual mu muDual
    S Sdual p pDual nextX nextY
  currentX_eq : (currentX : Int) =
    previous.wideRightInt - previous.wideLeftInt + 2 * padding
  nextX_eq : (nextX : Int) =
    current.wideRightInt - current.wideLeftInt + 2 * padding
  previousY_eq : previousY = currentY + 2 * padding
  currentY_eq : currentY = nextY + 2 * padding


end StatMech.FK.PeriodicPlanar

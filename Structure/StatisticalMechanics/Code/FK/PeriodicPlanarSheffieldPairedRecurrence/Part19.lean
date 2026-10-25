/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part26
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure DependentRadiusFirstAdjacentEndpointRow
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (template : Finset V) (step : Int) (cutoff : Nat)
    (epsilon B : Real) (r y s : Nat -> Real) (t : Nat -> Int)
    (minimumWidth minimumHeight : Nat -> Nat)
    (horizontalLeft horizontalRight : Nat -> Nat -> Int) where
  radius : Nat
  width : Nat
  height : Nat
  cutoff_le_radius : cutoff <= radius
  minimumWidth_le : minimumWidth radius <= width
  minimumHeight_le : minimumHeight radius <= height
  merge_lt : forall q : Fin 2 × (Fin 3 × Fin 3),
    mu.real (P.pairMergeErrorUnion template
      (template.image (P.shift (preferenceKingOffset q.2 +
        if q.1.val = 0 then 0 else verticalShift step))) radius) < epsilon
  dualVertical_gt : 1 - epsilon < muDual.real
    (Edual.verticalCrossingEvent (r radius) (r radius + width)
      ((2 * s radius + (s radius + t radius)) / 3)
      ((s radius + 2 * (s radius + t radius)) / 3))
  dualHorizontal_gt : 1 - epsilon < muDual.real
    (Edual.horizontalCrossingEvent
      (horizontalLeft radius width) (horizontalRight radius width)
      (y radius) (y radius + height))


end StatMech.FK.PeriodicPlanar

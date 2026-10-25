/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (template : Finset V) (widths : Finset Nat)
    (horizontalLeft horizontalRight : Nat -> Int)
    (y : Real) (minimumHeight cutoff : Nat)
    (endpointEpsilon mergeEpsilon : Real) where
  height : Nat
  radius : Nat
  minimumHeight_le : minimumHeight <= height
  cutoff_le_radius : cutoff <= radius
  horizontalEndpoint : forall width, width ∈ widths ->
    1 - endpointEpsilon < mu.real (E.horizontalCrossingEvent
      (horizontalLeft width) (horizontalRight width) y (y + height))
  merge : forall step : Nat, step <= height ->
    forall q : Fin 2 × (Fin 3 × Fin 3),
      mu.real (P.pairMergeErrorUnion template
        (template.image (P.shift (preferenceKingOffset q.2 +
          if q.1.val = 0 then 0 else verticalShift step))) radius) <
        mergeEpsilon


structure PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.VerticalEndpointExtension
    {E : PeriodicPlaneEmbedding P}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {template : Finset V} {widths : Finset Nat}
    {horizontalLeft horizontalRight : Nat -> Int}
    {y : Real} {minimumHeight cutoff : Nat}
    {endpointEpsilon mergeEpsilon : Real}
    (row : E.FiniteWidthEndpointMergeRow mu template widths
      horizontalLeft horizontalRight y minimumHeight cutoff
      endpointEpsilon mergeEpsilon)
    (verticalBottom verticalTop : Nat -> Int)
    (x : Real) (minimumWidth : Nat) (verticalEndpointEpsilon : Real) where
  width : Nat
  minimumWidth_le : minimumWidth <= width
  verticalEndpoint : forall step : Nat, step <= row.height ->
    1 - verticalEndpointEpsilon < mu.real (E.verticalCrossingEvent
      x (x + width) (verticalBottom step) (verticalTop step))


end StatMech.FK.PeriodicPlanar

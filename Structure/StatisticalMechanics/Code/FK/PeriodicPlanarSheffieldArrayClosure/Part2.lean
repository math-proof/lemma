/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part7
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

structure PeriodicPlaneEmbedding.AlignedSharedLevelStep
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Nat → Finset V) (p : Nat → Real)
    (family : ∀ m, E.NormalBoundaryBandFamily mu (S m) (p m))
    (verticalRequirement horizontalRequirement : Nat → Nat → Nat)
    (previousScale previousConnector : Nat)
    (scoreEpsilon mergeEpsilon : Real) where
  scale : Nat
  extent : Nat
  bottom : Finset V
  top : Finset V
  left : Finset V
  right : Finset V
  nextConnector : Nat
  scale_ge : previousScale ≤ scale
  connector_mono : previousConnector ≤ nextConnector
  threshold_gt : 1 - scoreEpsilon < p scale
  schedule : (family scale).AlignedMarginSchedule E
    (verticalRequirement scale) (horizontalRequirement scale)
  connector_subset :
    (P.orbitBox (P.bufferedRadius previousConnector) : Set V) ⊆
      E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  bottom_subset : (bottom : Set V) ⊆
    E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  bottomComponentScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (bottom : Set V) (E.rectBottomBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  top_subset : (top : Set V) ⊆
    E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  topComponentScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (top : Set V) (E.rectTopBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  left_subset : (left : Set V) ⊆
    E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  leftComponentScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (left : Set V) (E.rectLeftBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  right_subset : (right : Set V) ⊆
    E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  rightComponentScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (right : Set V) (E.rectRightBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  template_subset :
    (P.fourBoundaryComponentTemplate bottom top left right : Set V) ⊆
      E.rectVertices (-(extent : Real)) extent (-(extent : Real)) extent
  bottomScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (P.fourBoundaryComponentTemplate bottom top left right : Set V)
    (E.rectBottomBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  topScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (P.fourBoundaryComponentTemplate bottom top left right : Set V)
    (E.rectTopBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  leftScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (P.fourBoundaryComponentTemplate bottom top left right : Set V)
    (E.rectLeftBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  rightScore : p scale < mu.real (E.rectSideConnectionEvent
    (-(extent : Real)) extent (-(extent : Real)) extent
    (P.fourBoundaryComponentTemplate bottom top left right : Set V)
    (E.rectRightBoundaryVertices
      (-(extent : Real)) extent (-(extent : Real)) extent))
  verticalMerge :
    mu.real (P.pairMergeErrorUnion bottom top nextConnector) < mergeEpsilon
  horizontalMerge :
    mu.real (P.pairMergeErrorUnion left right nextConnector) < mergeEpsilon

end StatMech.FK.PeriodicPlanar

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

structure PeriodicPlaneEmbedding.CarriedCrossNestedArray
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) where
  a : Nat → Real
  b : Nat → Real
  c : Nat → Real
  d : Nat → Real
  aWide : Nat → Real
  bWide : Nat → Real
  cTall : Nat → Real
  dTall : Nat → Real
  bottom : Nat → Finset V
  top : Nat → Finset V
  left : Nat → Finset V
  right : Nat → Finset V
  verticalRadius : Nat → Nat
  horizontalRadius : Nat → Nat
  wideLeft : ∀ n, aWide n ≤ a n
  wideRight : ∀ n, b n ≤ bWide n
  tallBottom : ∀ n, cTall n ≤ c n
  tallTop : ∀ n, d n ≤ dTall n
  verticalConnector : ∀ n,
    (P.orbitBox (P.bufferedRadius (verticalRadius n)) : Set V) ⊆
      E.rectVertices (aWide n) (bWide n) (c n) (d n)
  horizontalConnector : ∀ n,
    (P.orbitBox (P.bufferedRadius (horizontalRadius n)) : Set V) ⊆
      E.rectVertices (a n) (b n) (cTall n) (dTall n)
  bottomLimit : Tendsto (fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (bottom n : Set V)
      (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))))
    atTop (nhds 1)
  topLimit : Tendsto (fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (top n : Set V)
      (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))))
    atTop (nhds 1)
  leftLimit : Tendsto (fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (left n : Set V)
      (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))))
    atTop (nhds 1)
  rightLimit : Tendsto (fun n ↦ mu.real
    (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
      (right n : Set V)
      (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))))
    atTop (nhds 1)
  verticalMergeLimit : Tendsto (fun n ↦ mu.real
    (P.pairMergeErrorUnion (bottom n) (top n) (verticalRadius n)))
    atTop (nhds 0)
  horizontalMergeLimit : Tendsto (fun n ↦ mu.real
    (P.pairMergeErrorUnion (left n) (right n) (horizontalRadius n)))
    atTop (nhds 0)

end StatMech.FK.PeriodicPlanar

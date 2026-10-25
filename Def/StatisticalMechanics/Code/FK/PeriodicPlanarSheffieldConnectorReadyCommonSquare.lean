/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldConnectorReadyCommonSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicPlaneEmbedding.UniformConnectorCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (radius : Nat -> Nat) : Prop :=
  forall (x : Nat -> Site 2)
    (ijVertical ijHorizontal : Nat -> Fin 3 × Fin 3)
    (a b c d : Nat -> Real),
    (forall n, (P.shift (x n) ''
      (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆
        E.rectVertices (a n) (b n) (c n) (d n)) ->
    (forall n,
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (x n)) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))) <=
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (x n)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n,
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (x n)) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n))) <=
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (x n)) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n,
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (x n + preferenceKingOffset (ijVertical n))) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))) <=
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (x n + preferenceKingOffset (ijVertical n))) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n,
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (x n + preferenceKingOffset (ijHorizontal n))) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n))) <=
      mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (x n + preferenceKingOffset (ijHorizontal n))) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    Tendsto (fun n => max
      (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n)))
      (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))))
      atTop (nhds 1)


end StatMech.FK.PeriodicPlanar

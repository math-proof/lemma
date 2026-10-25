/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part15
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

def PeriodicPlaneEmbedding.UniformTemplateDeepGridAdjacentHeightCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (template : Nat -> Finset V) (step : Nat -> Int)
    (radius : Nat -> Nat) : Prop :=
  forall (width height margin : Nat -> Nat)
    (hwidth : forall n, 0 < width n)
    (base : Nat -> Site 2)
    (vertical horizontal : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Bool)
    (a b c d epsilon : Nat -> Real)
    (bottom top left right : (n : Nat) ->
      PreferenceGridVertex (width n) (height n) -> Real),
    Tendsto epsilon atTop (nhds 0) ->
    (forall n, 0 <= epsilon n) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      ((template n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) <=
          E.rectVertices (a n) (b n) (c n) (d n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      margin n <= v.1.val -> v.1.val + margin n < width n ->
      margin n <= v.2.val -> v.2.val + margin n < height n ->
      (P.shift (base n + preferenceGridSite v) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n) (c n) (d n)) ->
    (forall n v, bottom n v = mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n v, top n v = mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n v, left n v = mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n v, right n v = mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n v, v.2.val <= margin n -> vertical n v = true) ->
    (forall n v, height n <= v.2.val + margin n ->
      vertical n v = false) ->
    (forall n v, v.1.val <= margin n -> horizontal n v = true) ->
    (forall n v, width n <= v.1.val + margin n ->
      horizontal n v = false) ->
    (forall n v, vertical n v = true ->
      top n v <= bottom n v + epsilon n) ->
    (forall n v, vertical n v = false ->
      bottom n v <= top n v + epsilon n) ->
    (forall n v, horizontal n v = true ->
      right n v <= left n v + epsilon n) ->
    (forall n v, horizontal n v = false ->
      left n v <= right n v + epsilon n) ->
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (a n) (b n) (c n) (d n)))
      (mu.real (E.verticalCrossingEvent
        (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1)

end StatMech.FK.PeriodicPlanar

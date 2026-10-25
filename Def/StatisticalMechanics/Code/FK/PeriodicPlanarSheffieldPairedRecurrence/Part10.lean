/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part19
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

def PeriodicPlaneEmbedding.UniformOutwardBoundaryCrossingRadius
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) (pad : Nat -> Int)
    (radius : Nat -> Nat) : Prop :=
  forall (width height : Nat -> Nat)
    (hwidth : forall n, 0 < width n)
    (hheight : forall n, 0 < height n)
    (base : Nat -> Site 2) (a b c d p : Nat -> Real),
    Tendsto p atTop (nhds 1) -> (forall n, p n <= 1) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      ((P.orbitBox n).image
        (P.shift (base n + preferenceGridSite v)) : Set V) <=
          E.rectVertices (a n) (b n) (c n) (d n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v +
          verticalShift (-(pad n))) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n)
            (c n - pad n) (d n - pad n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v +
          verticalShift (-(pad n))) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n) (b n)
            (c n - pad n) (d n + pad n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v +
          horizontalShift (-(pad n))) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n - pad n) (b n - pad n) (c n) (d n)) ->
    (forall n (v : PreferenceGridVertex (width n) (height n)),
      (P.shift (base n + preferenceGridSite v +
          horizontalShift (-(pad n))) ''
        (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
          E.rectVertices (a n - pad n) (b n + pad n) (c n) (d n)) ->
    (forall n (i : Fin (width n + 1)), p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (base n + preferenceGridSite
          (i, (0 : Fin (height n + 1))))) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n (i : Fin (width n + 1)), p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (base n + preferenceGridSite
          (i, Fin.last (height n)))) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n (j : Fin (height n + 1)), p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (base n + preferenceGridSite
          ((0 : Fin (width n + 1)), j))) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    (forall n (j : Fin (height n + 1)), p n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image (P.shift (base n + preferenceGridSite
          (Fin.last (width n), j))) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))) ->
    Tendsto (fun n => max
      (mu.real (E.verticalCrossingEvent
        (a n) (b n) (c n - pad n) (d n + pad n)))
      (mu.real (E.horizontalCrossingEvent
        (a n - pad n) (b n + pad n) (c n) (d n))))
      atTop (nhds 1)


end StatMech.FK.PeriodicPlanar

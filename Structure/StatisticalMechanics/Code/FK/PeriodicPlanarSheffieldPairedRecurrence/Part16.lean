/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part23
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure PairedBoundaryBandLevel
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))} {step : Nat -> Int}
    (data : PairedAdjacentBoundaryBandScheduleData
      E Edual mu muDual step) where
  a : Nat -> Real
  b : Nat -> Real
  c : Nat -> Real
  d : Nat -> Real
  width : Nat -> Nat
  height : Nat -> Nat
  margin : Nat -> Nat
  base : Nat -> Site 2
  widthDual : Nat -> Nat
  heightDual : Nat -> Nat
  marginDual : Nat -> Nat
  baseDual : Nat -> Site 2
  width_separated : forall n, 2 * margin n < width n
  height_separated : forall n, 2 * margin n < height n
  widthDual_separated : forall n, 2 * marginDual n < widthDual n
  heightDual_separated : forall n, 2 * marginDual n < heightDual n
  primal_source_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (((P.orbitBox n).image
      (P.shift (base n + preferenceGridSite v)) : Finset V) : Set V) <=
        E.rectVertices (a n) (b n) (c n) (d n)
  primal_connector_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    margin n <= v.1.val -> v.1.val + margin n < width n ->
    margin n <= v.2.val -> v.2.val + margin n < height n ->
    (P.shift (base n + preferenceGridSite v) ''
      (P.orbitBox (P.bufferedRadius (data.radius n)) : Set V)) <=
        E.rectVertices (a n) (b n) (c n) (d n)
  primal_bottom : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    v.2.val <= margin n -> data.score n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  primal_top : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    height n <= v.2.val + margin n -> data.score n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  primal_left : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    v.1.val <= margin n -> data.score n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  primal_right : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    width n <= v.1.val + margin n -> data.score n <= mu.real
      (E.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((P.orbitBox n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))
  dual_source_subset : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    (((Pdual.orbitBox n).image
      (Pdual.shift (baseDual n + preferenceGridSite v)) : Finset W) :
        Set W) <= Edual.rectVertices (a n) (b n) (c n) (d n)
  dual_connector_subset : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    marginDual n <= v.1.val ->
    v.1.val + marginDual n < widthDual n ->
    marginDual n <= v.2.val ->
    v.2.val + marginDual n < heightDual n ->
    (Pdual.shift (baseDual n + preferenceGridSite v) ''
      (Pdual.orbitBox
        (Pdual.bufferedRadius (data.radiusDual n)) : Set W)) <=
          Edual.rectVertices (a n) (b n) (c n) (d n)
  dual_bottom : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    v.2.val <= marginDual n -> data.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (baseDual n + preferenceGridSite v)) : Set W)
        (Edual.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  dual_top : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    heightDual n <= v.2.val + marginDual n ->
      data.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (baseDual n + preferenceGridSite v)) : Set W)
        (Edual.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  dual_left : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    v.1.val <= marginDual n -> data.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (baseDual n + preferenceGridSite v)) : Set W)
        (Edual.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  dual_right : forall n
      (v : PreferenceGridVertex (widthDual n) (heightDual n)),
    widthDual n <= v.1.val + marginDual n ->
      data.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (baseDual n + preferenceGridSite v)) : Set W)
        (Edual.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))


end StatMech.FK.PeriodicPlanar

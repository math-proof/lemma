/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part8
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure ExpandedEndpointPrimalBoundaryBandLevel
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (template : Nat -> Finset V) (radius : Nat -> Nat)
    (vLeft vRight vBottom vTop pad : Nat -> Real) where
  width : Nat -> Nat
  height : Nat -> Nat
  margin : Nat -> Nat
  base : Nat -> Site 2
  score : Nat -> Real
  width_separated : forall n, 2 * margin n < width n
  height_separated : forall n, 2 * margin n < height n
  score_le_one : forall n, score n <= 1
  score_tendsto : Tendsto score atTop (nhds 1)
  source_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    ((template n).image
      (P.shift (base n + preferenceGridSite v)) : Set V) <=
        E.rectVertices (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)
  connector_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    margin n <= v.1.val -> v.1.val + margin n < width n ->
    margin n <= v.2.val -> v.2.val + margin n < height n ->
    (P.shift (base n + preferenceGridSite v) ''
      (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <=
        E.rectVertices (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)
  bottom : forall n (v : PreferenceGridVertex (width n) (height n)),
    v.2.val <= margin n -> score n <= mu.real
      (E.rectSideConnectionEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices
          (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)))
  top : forall n (v : PreferenceGridVertex (width n) (height n)),
    height n <= v.2.val + margin n -> score n <= mu.real
      (E.rectSideConnectionEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices
          (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)))
  left : forall n (v : PreferenceGridVertex (width n) (height n)),
    v.1.val <= margin n -> score n <= mu.real
      (E.rectSideConnectionEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices
          (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)))
  right : forall n (v : PreferenceGridVertex (width n) (height n)),
    width n <= v.1.val + margin n -> score n <= mu.real
      (E.rectSideConnectionEvent
        (vLeft n - pad n) (vRight n + pad n)
        (vBottom n + pad n) (vTop n - pad n)
        ((template n).image
          (P.shift (base n + preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices
          (vLeft n - pad n) (vRight n + pad n)
          (vBottom n + pad n) (vTop n - pad n)))


end StatMech.FK.PeriodicPlanar

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part22
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

structure DualOutwardBoundaryBandLevel
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {step pad : Nat -> Int}
    (data : PairedAdjacentOutwardScheduleData
      E Edual mu muDual step pad) where
  a : Nat -> Real
  b : Nat -> Real
  c : Nat -> Real
  d : Nat -> Real
  width : Nat -> Nat
  height : Nat -> Nat
  base : Nat -> Site 2
  width_pos : forall n, 0 < width n
  height_pos : forall n, 0 < height n
  source_subset : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    ((Pdual.orbitBox n).image
      (Pdual.shift (base n + preferenceGridSite v)) : Set W) <=
        Edual.rectVertices (a n) (b n) (c n) (d n)
  connector_vertical_lower : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (Pdual.shift (base n + preferenceGridSite v +
        verticalShift (-(pad n))) ''
      (Pdual.orbitBox (Pdual.bufferedRadius
        (data.outwardRadiusDual n)) : Set W)) <=
      Edual.rectVertices (a n) (b n)
        (c n - pad n) (d n - pad n)
  connector_vertical_outer : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (Pdual.shift (base n + preferenceGridSite v +
        verticalShift (-(pad n))) ''
      (Pdual.orbitBox (Pdual.bufferedRadius
        (data.outwardRadiusDual n)) : Set W)) <=
      Edual.rectVertices (a n) (b n)
        (c n - pad n) (d n + pad n)
  connector_horizontal_lower : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (Pdual.shift (base n + preferenceGridSite v +
        horizontalShift (-(pad n))) ''
      (Pdual.orbitBox (Pdual.bufferedRadius
        (data.outwardRadiusDual n)) : Set W)) <=
      Edual.rectVertices (a n - pad n) (b n - pad n) (c n) (d n)
  connector_horizontal_outer : forall n
      (v : PreferenceGridVertex (width n) (height n)),
    (Pdual.shift (base n + preferenceGridSite v +
        horizontalShift (-(pad n))) ''
      (Pdual.orbitBox (Pdual.bufferedRadius
        (data.outwardRadiusDual n)) : Set W)) <=
      Edual.rectVertices (a n - pad n) (b n + pad n) (c n) (d n)
  bottom : forall n (i : Fin (width n + 1)),
    data.base.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (base n + preferenceGridSite
            (i, (0 : Fin (height n + 1))))) : Set W)
        (Edual.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))
  top : forall n (i : Fin (width n + 1)),
    data.base.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (base n + preferenceGridSite
            (i, Fin.last (height n)))) : Set W)
        (Edual.rectTopBoundaryVertices (a n) (b n) (c n) (d n)))
  left : forall n (j : Fin (height n + 1)),
    data.base.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (base n + preferenceGridSite
            ((0 : Fin (width n + 1)), j))) : Set W)
        (Edual.rectLeftBoundaryVertices (a n) (b n) (c n) (d n)))
  right : forall n (j : Fin (height n + 1)),
    data.base.scoreDual n <= muDual.real
      (Edual.rectSideConnectionEvent (a n) (b n) (c n) (d n)
        ((Pdual.orbitBox n).image
          (Pdual.shift (base n + preferenceGridSite
            (Fin.last (width n), j))) : Set W)
        (Edual.rectRightBoundaryVertices (a n) (b n) (c n) (d n)))


end StatMech.FK.PeriodicPlanar

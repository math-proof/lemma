/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDualBoundaryBands.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRecursiveLimits
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldNormalBoundaryBandAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualBoundaryBands
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


structure PairedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (muDual : Measure (ConfigSpace (Sym2 W)))
    (S : Finset V) (Sdual : Finset W) (p pDual : Real) where
  width : Nat
  height : Nat
  widthDual : Nat
  heightDual : Nat
  width_pos : 0 < width
  height_pos : 0 < height
  widthDual_pos : 0 < widthDual
  heightDual_pos : 0 < heightDual
  base : Site 2
  baseDual : Site 2
  narrowRight : Real
  shortTop : Real
  wideLeft : Real
  wideRight : Real
  tallTop : Real
  wideLeft_le : wideLeft ≤ 0
  narrowRight_le : narrowRight ≤ wideRight
  shortTop_le : shortTop ≤ tallTop
  primal_bottom : ∀ i : Fin (width + 1), p < mu.real
    (E.rectSideConnectionEvent wideLeft wideRight 0 shortTop
      (P.shift (base + preferenceGridSite
        (i, (0 : Fin (height + 1)))) '' (S : Set V))
      (E.rectBottomBoundaryVertices wideLeft wideRight 0 shortTop))
  primal_top : ∀ i : Fin (width + 1), p < mu.real
    (E.rectSideConnectionEvent wideLeft wideRight 0 shortTop
      (P.shift (base + preferenceGridSite
        (i, Fin.last height)) '' (S : Set V))
      (E.rectTopBoundaryVertices wideLeft wideRight 0 shortTop))
  primal_left : ∀ j : Fin (height + 1), p < mu.real
    (E.rectSideConnectionEvent 0 narrowRight 0 tallTop
      (P.shift (base + preferenceGridSite
        ((0 : Fin (width + 1)), j)) '' (S : Set V))
      (E.rectLeftBoundaryVertices 0 narrowRight 0 tallTop))
  primal_right : ∀ j : Fin (height + 1), p < mu.real
    (E.rectSideConnectionEvent 0 narrowRight 0 tallTop
      (P.shift (base + preferenceGridSite
        (Fin.last width, j)) '' (S : Set V))
      (E.rectRightBoundaryVertices 0 narrowRight 0 tallTop))
  dual_bottom : ∀ i : Fin (widthDual + 1), pDual < muDual.real
    (Edual.rectSideConnectionEvent wideLeft wideRight 0 shortTop
      (Pdual.shift (baseDual + preferenceGridSite
        (i, (0 : Fin (heightDual + 1)))) '' (Sdual : Set W))
      (Edual.rectBottomBoundaryVertices wideLeft wideRight 0 shortTop))
  dual_top : ∀ i : Fin (widthDual + 1), pDual < muDual.real
    (Edual.rectSideConnectionEvent wideLeft wideRight 0 shortTop
      (Pdual.shift (baseDual + preferenceGridSite
        (i, Fin.last heightDual)) '' (Sdual : Set W))
      (Edual.rectTopBoundaryVertices wideLeft wideRight 0 shortTop))
  dual_left : ∀ j : Fin (heightDual + 1), pDual < muDual.real
    (Edual.rectSideConnectionEvent 0 narrowRight 0 tallTop
      (Pdual.shift (baseDual + preferenceGridSite
        ((0 : Fin (widthDual + 1)), j)) '' (Sdual : Set W))
      (Edual.rectLeftBoundaryVertices 0 narrowRight 0 tallTop))
  dual_right : ∀ j : Fin (heightDual + 1), pDual < muDual.real
    (Edual.rectSideConnectionEvent 0 narrowRight 0 tallTop
      (Pdual.shift (baseDual + preferenceGridSite
        (Fin.last widthDual, j)) '' (Sdual : Set W))
      (Edual.rectRightBoundaryVertices 0 narrowRight 0 tallTop))


end StatMech.FK.PeriodicPlanar

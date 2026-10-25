/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


structure PeriodicPlaneEmbedding.NormalBoundaryBandSeed
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (margin : Nat) (p : Real) where
  baseLeft : Site 2
  baseRight : Site 2
  baseBottom : Site 2
  baseTop : Site 2
  radiusLeft : Nat
  radiusRight : Nat
  radiusBottom : Nat
  radiusTop : Nat
  left : ∀ i : Fin (margin + 1),
    P.shift (baseLeft + horizontalShift i.val) '' (S : Set V) ⊆
        E.rectVertices 0 radiusLeft (-(radiusLeft : Real)) radiusLeft ∧
      p < mu.real (E.rectSideConnectionEvent
        0 radiusLeft (-(radiusLeft : Real)) radiusLeft
        (P.shift (baseLeft + horizontalShift i.val) '' (S : Set V))
        (E.rectLeftBoundaryVertices
          0 radiusLeft (-(radiusLeft : Real)) radiusLeft))
  right : ∀ i : Fin (margin + 1),
    P.shift (baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(radiusRight : Real)) 0
          (-(radiusRight : Real)) radiusRight ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusRight : Real)) 0 (-(radiusRight : Real)) radiusRight
        (P.shift (baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectRightBoundaryVertices
          (-(radiusRight : Real)) 0 (-(radiusRight : Real)) radiusRight))
  bottom : ∀ i : Fin (margin + 1),
    P.shift (baseBottom + verticalShift i.val) '' (S : Set V) ⊆
        E.rectVertices (-(radiusBottom : Real)) radiusBottom
          0 radiusBottom ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusBottom : Real)) radiusBottom 0 radiusBottom
        (P.shift (baseBottom + verticalShift i.val) '' (S : Set V))
        (E.rectBottomBoundaryVertices
          (-(radiusBottom : Real)) radiusBottom 0 radiusBottom))
  top : ∀ i : Fin (margin + 1),
    P.shift (baseTop + verticalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(radiusTop : Real)) radiusTop
          (-(radiusTop : Real)) 0 ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusTop : Real)) radiusTop (-(radiusTop : Real)) 0
        (P.shift (baseTop + verticalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectTopBoundaryVertices
          (-(radiusTop : Real)) radiusTop (-(radiusTop : Real)) 0))


end StatMech.FK.PeriodicPlanar

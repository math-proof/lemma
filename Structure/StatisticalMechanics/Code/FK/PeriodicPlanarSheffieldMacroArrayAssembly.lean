/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdjacentHeight.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonSquareEnlarge
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


structure PeriodicPlaneEmbedding.NormalBoundaryBandFamily
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (p : Real) where
  baseLeft : Site 2
  baseRight : Site 2
  baseBottom : Site 2
  baseTop : Site 2
  radiusLeft : Nat → Nat
  radiusRight : Nat → Nat
  radiusBottom : Nat → Nat
  radiusTop : Nat → Nat
  left : ∀ (margin : Nat) (i : Fin (margin + 1)),
    P.shift (baseLeft + horizontalShift i.val) '' (S : Set V) ⊆
        E.rectVertices 0 (radiusLeft margin)
          (-(radiusLeft margin : Real)) (radiusLeft margin) ∧
      p < mu.real (E.rectSideConnectionEvent
        0 (radiusLeft margin) (-(radiusLeft margin : Real))
        (radiusLeft margin)
        (P.shift (baseLeft + horizontalShift i.val) '' (S : Set V))
        (E.rectLeftBoundaryVertices 0 (radiusLeft margin)
          (-(radiusLeft margin : Real)) (radiusLeft margin)))
  right : ∀ (margin : Nat) (i : Fin (margin + 1)),
    P.shift (baseRight + horizontalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(radiusRight margin : Real)) 0
          (-(radiusRight margin : Real)) (radiusRight margin) ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusRight margin : Real)) 0
        (-(radiusRight margin : Real)) (radiusRight margin)
        (P.shift (baseRight + horizontalShift (-(i.val : Int))) ''
          (S : Set V))
        (E.rectRightBoundaryVertices (-(radiusRight margin : Real)) 0
          (-(radiusRight margin : Real)) (radiusRight margin)))
  bottom : ∀ (margin : Nat) (i : Fin (margin + 1)),
    P.shift (baseBottom + verticalShift i.val) '' (S : Set V) ⊆
        E.rectVertices (-(radiusBottom margin : Real)) (radiusBottom margin)
          0 (radiusBottom margin) ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusBottom margin : Real)) (radiusBottom margin)
        0 (radiusBottom margin)
        (P.shift (baseBottom + verticalShift i.val) '' (S : Set V))
        (E.rectBottomBoundaryVertices (-(radiusBottom margin : Real))
          (radiusBottom margin) 0 (radiusBottom margin)))
  top : ∀ (margin : Nat) (i : Fin (margin + 1)),
    P.shift (baseTop + verticalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(radiusTop margin : Real)) (radiusTop margin)
          (-(radiusTop margin : Real)) 0 ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusTop margin : Real)) (radiusTop margin)
        (-(radiusTop margin : Real)) 0
        (P.shift (baseTop + verticalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectTopBoundaryVertices (-(radiusTop margin : Real))
          (radiusTop margin) (-(radiusTop margin : Real)) 0))


end StatMech.FK.PeriodicPlanar

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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part5
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}


structure PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (margin M : Nat) (p : Real) where
  zLeft : Site 2
  zRight : Site 2
  zBottom : Site 2
  zTop : Site 2
  left : ∀ i : Fin (margin + 1),
    P.shift (zLeft + horizontalShift i.val) '' (S : Set V) ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (zLeft + horizontalShift i.val) '' (S : Set V))
        (E.rectLeftBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  right : ∀ i : Fin (margin + 1),
    P.shift (zRight + horizontalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (zRight + horizontalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectRightBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  bottom : ∀ i : Fin (margin + 1),
    P.shift (zBottom + verticalShift i.val) '' (S : Set V) ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (zBottom + verticalShift i.val) '' (S : Set V))
        (E.rectBottomBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  top : ∀ i : Fin (margin + 1),
    P.shift (zTop + verticalShift (-(i.val : Int))) '' (S : Set V) ⊆
        E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        (P.shift (zTop + verticalShift (-(i.val : Int))) '' (S : Set V))
        (E.rectTopBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))

end StatMech.FK.PeriodicPlanar

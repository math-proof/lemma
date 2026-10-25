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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


structure PeriodicPlaneEmbedding.CommonSquareBoundaryBandData
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (width height M : Nat) (p : Real) where
  zLeft : Site 2
  zRight : Site 2
  zBottom : Site 2
  zTop : Site 2
  left : ∀ v : PreferenceGridVertex width height,
    ((S.image (P.shift zLeft)).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        ((S.image (P.shift zLeft)).image
          (P.shift (preferenceGridSite v)) : Set V)
        (E.rectLeftBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  right : ∀ v : PreferenceGridVertex width height,
    ((S.image (P.shift zRight)).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        ((S.image (P.shift zRight)).image
          (P.shift (preferenceGridSite v)) : Set V)
        (E.rectRightBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  bottom : ∀ v : PreferenceGridVertex width height,
    ((S.image (P.shift zBottom)).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        ((S.image (P.shift zBottom)).image
          (P.shift (preferenceGridSite v)) : Set V)
        (E.rectBottomBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))
  top : ∀ v : PreferenceGridVertex width height,
    ((S.image (P.shift zTop)).image
        (P.shift (preferenceGridSite v)) : Set V) ⊆
          E.rectVertices (-(M : Real)) M (-(M : Real)) M ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(M : Real)) M (-(M : Real)) M
        ((S.image (P.shift zTop)).image
          (P.shift (preferenceGridSite v)) : Set V)
        (E.rectTopBoundaryVertices
          (-(M : Real)) M (-(M : Real)) M))

end StatMech.FK.PeriodicPlanar

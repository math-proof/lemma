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
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandAssembly
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


structure PeriodicPlaneEmbedding.BoundaryBandSeed
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (S : Finset V) (width height : Nat) (p : Real) where
  baseLeft : Site 2
  baseRight : Site 2
  baseBottom : Site 2
  baseTop : Site 2
  radiusLeft : Nat
  radiusRight : Nat
  radiusBottom : Nat
  radiusTop : Nat
  left : ∀ v : PreferenceGridVertex width height,
    P.shift (baseLeft + preferenceGridSite v) '' (S : Set V) ⊆
        E.rectVertices 0 radiusLeft (-(radiusLeft : Real)) radiusLeft ∧
      p < mu.real (E.rectSideConnectionEvent
        0 radiusLeft (-(radiusLeft : Real)) radiusLeft
        (P.shift (baseLeft + preferenceGridSite v) '' (S : Set V))
        (E.rectLeftBoundaryVertices
          0 radiusLeft (-(radiusLeft : Real)) radiusLeft))
  right : ∀ v : PreferenceGridVertex width height,
    P.shift (baseRight + preferenceGridSite v) '' (S : Set V) ⊆
        E.rectVertices (-(radiusRight : Real)) 0
          (-(radiusRight : Real)) radiusRight ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusRight : Real)) 0 (-(radiusRight : Real)) radiusRight
        (P.shift (baseRight + preferenceGridSite v) '' (S : Set V))
        (E.rectRightBoundaryVertices
          (-(radiusRight : Real)) 0 (-(radiusRight : Real)) radiusRight))
  bottom : ∀ v : PreferenceGridVertex width height,
    P.shift (baseBottom + preferenceGridSite v) '' (S : Set V) ⊆
        E.rectVertices (-(radiusBottom : Real)) radiusBottom
          0 radiusBottom ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusBottom : Real)) radiusBottom 0 radiusBottom
        (P.shift (baseBottom + preferenceGridSite v) '' (S : Set V))
        (E.rectBottomBoundaryVertices
          (-(radiusBottom : Real)) radiusBottom 0 radiusBottom))
  top : ∀ v : PreferenceGridVertex width height,
    P.shift (baseTop + preferenceGridSite v) '' (S : Set V) ⊆
        E.rectVertices (-(radiusTop : Real)) radiusTop
          (-(radiusTop : Real)) 0 ∧
      p < mu.real (E.rectSideConnectionEvent
        (-(radiusTop : Real)) radiusTop (-(radiusTop : Real)) 0
        (P.shift (baseTop + preferenceGridSite v) '' (S : Set V))
        (E.rectTopBoundaryVertices
          (-(radiusTop : Real)) radiusTop (-(radiusTop : Real)) 0))


end StatMech.FK.PeriodicPlanar

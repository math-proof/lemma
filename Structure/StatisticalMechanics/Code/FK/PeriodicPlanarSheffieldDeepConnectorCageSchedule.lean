/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorCageSchedule.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorRows.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldExclusion
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarDualBurtonKeane.Part2
open MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

structure SymmetricBandDeepConnectorCageCertificate
    (D : PeriodicPlanarDualPair P Pdual)
    (B rPrimal Rdeep rDual : Real) (band width : Nat)
    (L U : Finset V) where
  Rcage : Real
  C : Real
  D0 : Real
  A : Real
  Tbottom : Real
  Ttop : Real
  rightGap : C - 4 * B + B < D0 + 4 * B
  lowerSources : ∀ x ∈ L,
    D.primalEmbedding.vertexCoord x 1 < C - 4 * B
  upperSources : ∀ y ∈ U,
    D0 + 4 * B < D.primalEmbedding.vertexCoord y 1
  width_eq : A + 4 * B = Rdeep ∧
    Rdeep + width = Rcage - 4 * B
  lowerCorridor :
    D.primalEmbedding.infiniteOpenBoundaryConnectionTo
        rPrimal (L : Set V)
        (D.primalEmbedding.lowerBoundaryRayVertices
          rPrimal (-(band : Real))) ⊆
      D.primalEmbedding.horizontalCrossingEvent
        (rDual - 5 * B) (Rcage + 5 * B)
        (C + 4 * B) (Tbottom - 4 * B)
  upperCorridor :
    D.primalEmbedding.infiniteOpenBoundaryConnectionTo
        rPrimal (U : Set V)
        (D.primalEmbedding.upperBoundaryRayVertices rPrimal band) ⊆
      D.primalEmbedding.horizontalCrossingEvent
        (rDual - 5 * B) (Rcage + 5 * B)
        (Ttop + 4 * B) (D0 - 4 * B)
  dual_left_lt_right : rDual < Rcage
  rightWidth : A + 10 * B < Rcage
  bottomGap : C + 10 * B < Tbottom
  topGap : Ttop + 10 * B < D0
  rootRight : rDual + B ≤ A
  rootBottom : Tbottom < -(band : Real)
  rootTop : (band : Real) < Ttop
  rectBottom : C ≤ -(band : Real)
  rectTop : (band : Real) ≤ D0


end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar

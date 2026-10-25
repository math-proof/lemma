/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldDeepConnectorRows.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOpenBoundaryCrossover
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorMeasureClosure.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepConnectorRows
open Filter MeasureTheory Set


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


variable {W : Type*} [DecidableEq W] [Countable W]
  {Pdual : PeriodicGraph W}

namespace PeriodicPlanarDualPair

theorem complementaryDual_rightHalfPlane_measure_eq_zero_of_separatedRows
    (D : PeriodicPlanarDualPair P Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hdualErgodic : Pdual.IsErgodic (D.dualMeasure mu))
    (hdualUnique : D.dualMeasure mu
      {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (rDual : Real) {r R : Real} (hrR : r ≤ R)
    (s : Nat → Real) (t : Nat → Int)
    (hdisjoint : ∀ (band : Nat) (L U : Finset V) (width : Nat),
      (L : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      (U : Set V) ⊆ D.primalEmbedding.rightHalfPlaneVertices R →
      U = L.image (P.shift (verticalShift (1 + t band))) →
      Disjoint
        (D.primalEmbedding.finiteDeepOpenExitedJoinedBoundaryArmEvent
          r R (s band) (s band + t band) width L U)
        ((dualConfigEquiv D.edgeDual) ⁻¹'
          D.dualEmbedding.rightHalfPlaneBoundaryBandHasInfiniteCluster
            rDual (-(band : Real)) band)) :
    D.dualMeasure mu
      (D.dualEmbedding.rightHalfPlaneHasInfiniteCluster rDual) = 0 := by
  apply
    D.complementaryDual_rightHalfPlane_measure_eq_zero_of_finiteDeepConnector_schedules
      mu hdualErgodic hdualUnique rDual
  intro band
  exact D.finiteDeepConnectorBandSchedule_of_separatedRows
    mu hFKG hTI hunique rDual band hrR (s band) (t band)
      (hdisjoint band)

end PeriodicPlanarDualPair
end StatMech.FK.PeriodicPlanar

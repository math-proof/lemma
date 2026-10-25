/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotatedBoundaryBands.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDualBoundaryBands.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotatedBoundaryBands
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

theorem exists_pairedRotatedMixedBoundaryScores
    (E : PeriodicPlaneEmbedding P) (Edual : PeriodicPlaneEmbedding Pdual)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (muDual : Measure (ConfigSpace (Sym2 W)))
      [IsProbabilityMeasure muDual]
    (hTI : P.IsTranslationInvariant mu)
    (hTIDual : Pdual.IsTranslationInvariant muDual)
    {S : Finset V} {Sdual : Finset W} {p pDual : Real}
    (family : E.NormalBoundaryBandFamily mu S p)
    (familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual)
    {verticalRequirement horizontalRequirement : Nat → Nat}
    (schedule : PairedAlignedMarginSchedule E Edual family familyDual
      verticalRequirement horizontalRequirement)
    (k : Nat) :
    Nonempty (PairedMixedBoundaryScores E.axisSwap Edual.axisSwap mu muDual
      S Sdual p pDual) := by
  exact exists_pairedMixedBoundaryScores E.axisSwap Edual.axisSwap
    mu muDual (P.axisSwap_isTranslationInvariant mu hTI)
    (Pdual.axisSwap_isTranslationInvariant muDual hTIDual)
    family.axisSwap familyDual.axisSwap
    schedule.axisSwap k

end StatMech.FK.PeriodicPlanar

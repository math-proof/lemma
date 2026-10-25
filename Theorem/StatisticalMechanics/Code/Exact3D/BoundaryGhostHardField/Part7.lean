/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/BoundaryGhostHardField.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteHardField.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Def.StatisticalMechanics.Code.Exact3D.BoundaryGhostHardField.Part6
open Filter
open scoped BigOperators Topology


namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical_proved :
    FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical := by
  intro β hβpos _hβc
  exact Eventually.of_forall fun n =>
    finiteBoundaryGhostAlignedLimitIdentification_of_pos 3 n hβpos


theorem
    finiteBoundaryGhostCountFactorDictionaryPositiveSubcritical_of_alignedLimit
    (hdict :
      FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical) :
    FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical := by
  intro β hβpos hβc
  exact (hdict β hβpos hβc).mono (fun n hn => by
    exact
      ⟨boundaryGhostOriginalBase 3 n β, boundaryGhostOnePointObservable 3 n,
        finiteBoundaryGhostCountFactorDictionary_of_alignedLimitIdentification
          hn⟩)


theorem finiteBoundaryGhostFactorDictionaryPositiveSubcritical_of_countFactor
    (hdict : FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical) :
    FiniteBoundaryGhostFactorDictionaryPositiveSubcritical := by
  intro β hβpos hβc
  exact (hdict β hβpos hβc).mono (fun n hn => by
    rcases hn with ⟨base, obs, D⟩
    exact
      ⟨base, obs, boundaryGhostAlignedLimitFactor 3 n,
        boundaryGhostCountFactor 3 n β,
        finiteBoundaryGhostFactorDictionary_of_countFactorDictionary D⟩)


theorem finiteQ2SimonBoundaryGhostHardFieldLimit_of_factorDictionary
    (hdict : FiniteBoundaryGhostFactorDictionaryPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical := by
  intro β hβpos hβc
  exact (hdict β hβpos hβc).mono (fun n hn => by
    rcases hn with ⟨base, obs, limitFactor, factor, D⟩
    exact
      finiteBoundaryGhostCurrentOnePoint_tendsto_wired_of_factorDictionary
        (D := D))


theorem finiteQ2SimonBoundaryGhostHardFieldLimit_of_countFactorDictionary
    (hdict : FiniteBoundaryGhostCountFactorDictionaryPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostHardFieldLimit_of_factorDictionary
    (finiteBoundaryGhostFactorDictionaryPositiveSubcritical_of_countFactor hdict)


theorem finiteQ2SimonBoundaryGhostHardFieldLimit_of_alignedLimit
    (hdict :
      FiniteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostHardFieldLimit_of_countFactorDictionary
    (finiteBoundaryGhostCountFactorDictionaryPositiveSubcritical_of_alignedLimit
      hdict)


theorem finiteQ2SimonBoundaryGhostHardFieldLimit_from_exactAlignedSector :
    FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostHardFieldLimit_of_alignedLimit
    finiteBoundaryGhostAlignedLimitIdentificationPositiveSubcritical_proved


theorem finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector :
    FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical :=
  finiteBoundaryGhostApprox_of_hardFieldLimit
    finiteQ2SimonBoundaryGhostHardFieldLimit_from_exactAlignedSector


theorem finiteCurrentSimon_of_exactBoundaryGhostComparison
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical :=
  finiteCurrentSimon_of_boundaryGhostApprox_comparison
    finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector hcompare


theorem finiteIsingSimon_of_exactBoundaryGhostComparison
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical :=
  finiteIsingSimon_of_boundaryGhostApprox_comparison
    finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector hcompare


theorem freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostComparison
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_comparison
    finiteQ2SimonBoundaryGhostApprox_from_exactAlignedSector hcompare


theorem freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_finiteFK
    (freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostComparison
      hcompare)


theorem finiteCurrentSimon_of_exactBoundaryGhostFirstExitPositive
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical :=
  finiteCurrentSimon_of_exactBoundaryGhostComparison
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)


theorem finiteIsingSimon_of_exactBoundaryGhostFirstExitPositive
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical :=
  finiteIsingSimon_of_exactBoundaryGhostComparison
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)


theorem freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostFirstExitPositive
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_exactBoundaryGhostComparison
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)


theorem freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostFirstExitPositive
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FreeQ2BoundaryProfileSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileSimonFreeSum_of_exactBoundaryGhostComparison
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)

end Exact3D
end StatMech

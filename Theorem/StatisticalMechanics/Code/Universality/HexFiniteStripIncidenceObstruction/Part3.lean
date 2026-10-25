/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction.Part2


namespace StatMech.Universality

open Complex HexWalk Set


theorem hexEmptyIncidenceBoundaryData_no_incidences
    (R : HexFiniteRegion) (h0 : ℤ) :
    (hexEmptyIncidenceDomain R h0).incidences = ∅ :=
  hexEmptyIncidenceDomain_incidences R h0


theorem hexEmptyIncidenceBoundaryData_topContour_eq
    (R : HexFiniteRegion) (h0 : ℤ) :
    hexContourUpsilon R.inRegion R.start h0
      (hexEmptyIncidenceBoundaryData R h0).sides hexChi = hexChi :=
  (hexEmptyIncidenceBoundaryData R h0).ups_eq.symm

theorem hexEmptyIncidenceBoundaryData_topContour_ne_zero
    (R : HexFiniteRegion) (h0 : ℤ) :
    hexContourUpsilon R.inRegion R.start h0
      (hexEmptyIncidenceBoundaryData R h0).sides hexChi ≠ 0 := by
  rw [hexEmptyIncidenceBoundaryData_topContour_eq]
  exact ne_of_gt hexChi_pos


end StatMech.Universality

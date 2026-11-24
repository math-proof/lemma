module
public import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
public import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
public import Def.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex HexWalk Set


@[simp] theorem hexEmptyIncidenceDomain_incidences
    (R : HexFiniteRegion) (h0 : ℤ) :
    (hexEmptyIncidenceDomain R h0).incidences = ∅ := by
  simp [HexDomain.incidences, hexEmptyIncidenceDomain]


end StatMech.Universality

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripIncidenceObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripNormalizedBoundary.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryPhases.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripIncidenceObstruction


namespace StatMech.Universality

open Complex HexWalk Set


noncomputable def hexEmptyIncidenceDomain
    (R : HexFiniteRegion) (h0 : ℤ) : HexDomain (Fin 0) where
  interiorVertices := ∅
  pos := fun v => Fin.elim0 v
  mid := fun v => Fin.elim0 v
  obs := fun z => parafObservable R.inRegion R.start h0 z (5 / 8) hexChi
  relation := by
    intro v
    exact Fin.elim0 v


end StatMech.Universality

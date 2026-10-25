/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexGenuineStripStartGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexStartPhaseRepair.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBoundaryUncond.Part2
import Def.StatisticalMechanics.Code.Universality.HexGenuineStripStartGeometry


namespace StatMech.Universality

open Complex HexWalk Set

open scoped BigOperators


noncomputable abbrev hexGenuineStripRegion : HexFiniteRegion :=
  hexVBCRegion hexGenuineStripStart 1

noncomputable abbrev hexGenuineStripDomain : HexDomain (Fin 1) :=
  hexUncondDomain hexGenuineStripStart 1

noncomputable abbrev hexGenuineStripPairing :
    hexGenuineStripDomain.InteriorPairing :=
  hexUncondPairing hexGenuineStripStart 1


end StatMech.Universality

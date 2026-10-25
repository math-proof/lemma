/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PropIVGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.InteriorRegion.Part5
import Theorem.StatisticalMechanics.Code.Onsager.ChordCut.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2


namespace StatMech.Onsager.PropIVGeneral

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches

open StatMech.Onsager.WindingBridge

open StatMech.Onsager.InteriorRegion


def fromSite (x : Site 2) : Pt := (x 0, x 1)

end StatMech.Onsager.PropIVGeneral

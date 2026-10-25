/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorRegion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingBridge.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2


namespace StatMech.Onsager.InteriorRegion

open StatMech.Lattice

open StatMech.Onsager.ChordCut

open StatMech.Onsager.InteriorReaches

open StatMech.Onsager.WindingBridge


def liftS (P : Finset Pt) : Set (Site 2) := toSite '' (P : Set Pt)


end StatMech.Onsager.InteriorRegion
